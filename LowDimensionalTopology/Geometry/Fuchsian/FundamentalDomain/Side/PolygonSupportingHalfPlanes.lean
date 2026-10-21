/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSides
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology Filter
open scoped Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Surfaces

/-- The whole original polygon and every nonidentity translate admit a strict global Klein separator. -/
theorem IsConvexFuchsianPolygon.exists_global_tile_separator
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (g : H) (hg : g ≠ 1) :
    ∃ (n : ℂ) (t : ℝ), n ≠ 0 ∧
      (∀ x ∈ D, inner ℝ n (P.kleinCoordinate x) < t) ∧
      (∀ x ∈ g • D, t < inner ℝ n (P.kleinCoordinate x)) := by
  let F := P.kleinCoordinate
  have hF := P.kleinCoordinate_isOpenEmbedding
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hc : Convex ℝ (F '' (g • D)) := by
    change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x)) '' (g • D))
    rw [← image_image]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp (hD.smul_convex g)
  have hd : Disjoint (F '' D) (F '' (g • D)) :=
    (hD.locallyFinite.fundamental.disjoint_image hg).symm.image hF.injective.injOn
      (subset_univ _) (subset_univ _)
  obtain ⟨n,t,hn,hl,hr⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator hD.klein_convex
    (hF.isOpenMap _ hDo) (hDn.image F) hc
    (hF.isOpenMap _ ((Homeomorph.smul g).isOpenMap _ hDo))
    ((hDn.image (fun x => g • x)).image F) hd
  exact ⟨n,t,hn,fun x hx => hl _ ⟨x,hx,rfl⟩,fun x hx => hr _ ⟨x,hx,rfl⟩⟩

/-- Actual closed tiles satisfy the corresponding weak global separator inequalities. -/
theorem polygon_tile_separator_closures
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} {g : H} {n : ℂ} {t : ℝ}
    (hl : ∀ x ∈ D, inner ℝ n (P.kleinCoordinate x) < t)
    (hr : ∀ x ∈ g • D, t < inner ℝ n (P.kleinCoordinate x)) :
    (∀ x ∈ closure D, inner ℝ n (P.kleinCoordinate x) ≤ t) ∧
    (∀ x ∈ fuchsianDomainTile P D g, t ≤ inner ℝ n (P.kleinCoordinate x)) := by
  have hc : Continuous (fun x => inner ℝ n (P.kleinCoordinate x)) :=
    continuous_const.inner P.kleinCoordinate_isOpenEmbedding.continuous
  have hleft : closure D ⊆ {x | inner ℝ n (P.kleinCoordinate x) ≤ t} :=
    closure_minimal (fun x hx => (hl x hx).le) (isClosed_le hc continuous_const)
  have hright : closure (g • D) ⊆ {x | t ≤ inner ℝ n (P.kleinCoordinate x)} :=
    closure_minimal (fun x hx => (hr x hx).le) (isClosed_le continuous_const hc)
  refine ⟨fun x hx => hleft hx,fun x hx => hright ?_⟩
  have he : g • closure D = closure (g • D) := (Homeomorph.smul g).image_closure D
  rw [← he]
  exact hx

/-- Every actual polygon side lies on a globally supporting affine Klein line. -/
theorem IsConvexFuchsianPolygon.side_global_support
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) :
    ∃ (n : ℂ) (t : ℝ), n ≠ 0 ∧
      (∀ x ∈ D, inner ℝ n (P.kleinCoordinate x) < t) ∧
      (∀ x ∈ closure D, inner ℝ n (P.kleinCoordinate x) ≤ t) ∧
      (∀ x ∈ S, inner ℝ n (P.kleinCoordinate x) = t) := by
  obtain ⟨⟨g,hg,rfl⟩,_⟩ := hS
  obtain ⟨n,t,hn,hl,hr⟩ := hD.exists_global_tile_separator g hg
  obtain ⟨hcl,hcr⟩ := polygon_tile_separator_closures hl hr
  exact ⟨n,t,hn,hl,hcl,fun x hx => le_antisymm (hcl x hx.1) (hcr x hx.2)⟩

/-- A countable family of strict global Klein half-planes has literal intersection equal to the original polygon. -/
theorem IsConvexFuchsianPolygon.exists_countable_halfplane_intersection
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    ∃ (n : {g : H // g ≠ 1} → ℂ) (t : {g : H // g ≠ 1} → ℝ),
      (∀ g, n g ≠ 0) ∧
      (∀ g, ∀ x ∈ D, inner ℝ (n g) (P.kleinCoordinate x) < t g) ∧
      (∀ g, ∀ x ∈ (g.val • D), t g < inner ℝ (n g) (P.kleinCoordinate x)) ∧
      D = ⋂ g, {x | inner ℝ (n g) (P.kleinCoordinate x) < t g} := by
  classical
  have he (g : {g : H // g ≠ 1}) := hD.exists_global_tile_separator g.val g.property
  choose n t hn hl hr using he
  refine ⟨n,t,hn,hl,hr,?_⟩
  ext x
  constructor
  · exact fun hx => mem_iInter.mpr (fun g => hl g x hx)
  · intro hx
    by_contra hxD
    obtain ⟨g,hgx⟩ : ∃ g : H, g ≠ 1 ∧ x ∈ fuchsianDomainTile P D g := by
      by_cases hxcl : x ∈ closure D
      · have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
        have hxf : x ∈ frontier D := by
          simpa only [frontier,hDo.interior_eq,Set.mem_sdiff] using And.intro hxcl hxD
        obtain ⟨g,hg,hgx⟩ := hD.boundary_mate hxf
        exact ⟨g⁻¹,inv_ne_one.mpr hg,⟨g • x,frontier_subset_closure hgx,inv_smul_smul g x⟩⟩
      · have hcover := hD.locallyFinite.fundamental.closure_cover
        have hmem : x ∈ ⋃ g : H, fuchsianDomainTile P D g := by
          change x ∈ ⋃ g : H, (fun z : P.domain.carrier => g • z) '' closure D
          rw [hcover]
          trivial
        obtain ⟨g,hg⟩ := mem_iUnion.mp hmem
        refine ⟨g,?_,hg⟩
        intro h1
        apply hxcl
        simpa only [h1,fuchsianDomainTile,one_smul] using hg
    let j : {g : H // g ≠ 1} := ⟨g,hgx.1⟩
    have hlt := mem_iInter.mp hx j
    have hge := (polygon_tile_separator_closures (hl j) (hr j)).2 x hgx.2
    exact hlt.not_ge hge

/-- A strict affine Klein cut which has native points on both sides is bounded by a genuine native geodesic. -/
theorem exists_discLine_of_straddling_klein_cut (n : ℂ) (t : ℝ) (hn : n ≠ 0)
    (a b : Complex.UnitDisc) (ha : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate a) < t)
    (hb : t < inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate b)) :
    ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine, ∀ z : Complex.UnitDisc,
      z ∈ L.carrier ↔ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = t := by
  have hpre : IsPreconnected ((fun z : ℂ => inner ℝ n z) '' Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected.image _
      (continuous_const.inner continuous_id).continuousOn
  have hball (z : Complex.UnitDisc) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact mem_range_self z
  obtain ⟨x,hx,hxe⟩ := hpre.ordConnected.out
    (mem_image_of_mem (fun z : ℂ => inner ℝ n z) (hball a))
    (mem_image_of_mem (fun z : ℂ => inner ℝ n z) (hball b)) ⟨ha.le,hb.le⟩
  let m := Complex.I * n
  have hm : m ≠ 0 := mul_ne_zero Complex.I_ne_zero hn
  have hnm : inner ℝ n m = 0 := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    simp [m,Complex.mul_re,Complex.mul_im]
    ring
  have hc : Continuous (fun r : ℝ => x + r • m) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Tendsto (fun r : ℝ => x + r • m) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), x + r • m ∈ Metric.ball (0 : ℂ) 1 :=
    htend.eventually (Metric.isOpen_ball.mem_nhds hx)
  obtain ⟨r,hrball,hrpos⟩ := (hevent.and (self_mem_nhdsWithin :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r)).exists
  let y := x + r • m
  have hyne : y ≠ x := by
    intro he
    have he' : x + r • m = x + 0 := by simpa only [add_zero] using he
    have hz : r • m = 0 := add_left_cancel he'
    exact (smul_ne_zero hrpos.ne' hm) hz
  have hye : inner ℝ n y = t := by
    simp only [y,inner_add_right,real_inner_smul_right,hnm,mul_zero,add_zero,hxe]
  obtain ⟨u,hu⟩ : x ∈ range _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact hx
  obtain ⟨v,hv⟩ : y ∈ range _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    exact hrball
  have huv : u ≠ v := by
    intro he
    exact hyne (hv.symm.trans ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate he).symm.trans hu))
  obtain ⟨L,⟨huL,hvL⟩,_⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_through u v huv
  obtain ⟨q,s,hq,hL⟩ := L.exists_klein_linear_equation
  refine ⟨L,fun z => ?_⟩
  have he := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points hn hq
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.ne huv) (hu ▸ hxe) (hv ▸ hye)
    ((hL u).mp huL) ((hL v).mp hvL) (x := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)
  exact (hL z).trans he.symm

/-- Countably many actual complementary components of native geodesics cut out the whole original polygon. -/
theorem IsConvexFuchsianPolygon.exists_countable_geodesic_halfplane_intersection
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Countable {g : H // g ≠ 1} ∧
    ∃ (a : P.domain.carrier) (L : {g : H // g ≠ 1} → _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine), a ∈ D ∧
      (∀ g, P.finiteCoordinate a ∉ (L g).carrier) ∧
      D = ⋂ g, P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L g) (P.finiteCoordinate a) := by
  classical
  have hc : Countable {g : H // g ≠ 1} := by
    let : Countable H := P.countable
    infer_instance
  refine ⟨hc,?_⟩
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  obtain ⟨a,ha⟩ := hDn
  obtain ⟨n,t,hn,hl,hr,hinter⟩ := hD.exists_countable_halfplane_intersection
  have hline (g : {g : H // g ≠ 1}) : ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine, ∀ z : Complex.UnitDisc,
      z ∈ L.carrier ↔ inner ℝ (n g) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = t g := by
    have hb : g.val • a ∈ g.val • D := ⟨a,ha,rfl⟩
    exact exists_discLine_of_straddling_klein_cut (n g) (t g) (hn g)
      (P.finiteCoordinate a) (P.finiteCoordinate (g.val • a))
      (hl g a ha) (hr g (g.val • a) hb)
  choose L hL using hline
  have hhalf (g : {g : H // g ≠ 1}) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L g) (P.finiteCoordinate a) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt (n g) (t g) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.connectedComponentIn_discLine_lt (L g) (n g) (t g) (hL g)
      (P.finiteCoordinate a) (hl g a ha)
  refine ⟨a,L,ha,?_,?_⟩
  · intro g hmem
    exact (hl g a ha).ne ((hL g (P.finiteCoordinate a)).mp hmem)
  · rw [hinter]
    congr 1
    funext g
    rw [hhalf]
    rfl

end LowDimensionalTopology.Geometry.Fuchsian
