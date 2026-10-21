module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.CosetRegion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CosetFundamentalDomains

/-! Genuine point-stabilizer Dirichlet regions, allowing an elliptic center. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Pointwise OnePoint UpperHalfPlane Complex.UnitDisc RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section
local instance stabilizerDirichletSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance stabilizerDirichletSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Compare the center with its genuinely different orbit points, retaining the full point stabilizer. -/
def stabilizerDirichletRegion {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : Set P.domain.carrier :=
  {z | ∀ g : H, g • w ≠ w → z ∈ dirichletHalfPlane P w g}

theorem stabilizerDirichletRegion_center_mem {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : w ∈ stabilizerDirichletRegion P w := by
  intro g hg
  change P.hyperbolicDist w w < P.hyperbolicDist w (g • w)
  rw [P.hyperbolicDist_self]
  exact P.hyperbolicDist_pos.mpr (Ne.symm hg)

theorem stabilizerDirichletRegion_isOpen {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : IsOpen (stabilizerDirichletRegion P w) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  let J:={g : H | g • w≠w ∧ P.hyperbolicDist (g • w) w≤2*(P.hyperbolicDist w z+1)}
  have hJ : J.Finite:=(P.bounded_orbit_labels w w _).subset (fun _ h=>h.2)
  have hV : (⋂g∈J,dirichletHalfPlane P w g)∈𝓝 z:=
    (biInter_mem hJ).mpr (fun g hg=>(dirichletHalfPlane_isOpen P w g).mem_nhds (hz g hg.1))
  have hB : {u | P.hyperbolicDist u z<1}∈𝓝 z:=by
    apply (isOpen_lt (P.hyperbolicDist_left_continuous z) continuous_const).mem_nhds
    change P.hyperbolicDist z z<1
    rw [P.hyperbolicDist_self]
    norm_num
  apply Filter.mem_of_superset (inter_mem hB hV)
  rintro u ⟨huB,huV⟩ g hg
  by_cases hgJ : g∈J
  · exact mem_iInter₂.mp huV g hgJ
  · have hfar : 2*(P.hyperbolicDist w z+1)<P.hyperbolicDist (g • w) w:=
      not_le.mp (fun hle=>hgJ ⟨hg,hle⟩)
    change P.hyperbolicDist u z<1 at huB
    have hwu:=P.hyperbolicDist_triangle w z u
    rw [P.hyperbolicDist_comm z u] at hwu
    have ht:=P.hyperbolicDist_triangle w u (g • w)
    rw [P.hyperbolicDist_comm w (g • w)] at ht
    have hc:=P.hyperbolicDist_comm w u
    change P.hyperbolicDist u w<P.hyperbolicDist u (g • w)
    linarith

theorem stabilizerDirichletRegion_convex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' stabilizerDirichletRegion P w) := by
  have he : P.finiteCoordinate '' stabilizerDirichletRegion P w=
      ⋂g : H,⋂hg : g • w≠w,P.finiteCoordinate '' dirichletHalfPlane P w g:=by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact mem_iInter.mpr (fun g=>mem_iInter.mpr (fun hg=>mem_image_of_mem _ (hx g hg)))
    · intro hz
      refine ⟨P.finiteCoordinate.symm z,?_,P.finiteCoordinate.apply_symm_apply z⟩
      intro g hg
      obtain ⟨x,hx,hxz⟩:=mem_iInter₂.mp hz g hg
      have heq : x=P.finiteCoordinate.symm z:=P.finiteCoordinate.injective (hxz.trans
        (P.finiteCoordinate.apply_symm_apply z).symm)
      exact heq ▸ hx
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.iInter (fun
    g=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.iInter (fun _=>dirichletHalfPlane_convex P w g))


def stabilizerDirichletKleinClosed {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : Set ℂ :=
  {u | ∀g : H,g • w≠w → inner ℝ (dirichletCutNormal P w g) u≤dirichletCutThreshold P w g}

theorem stabilizerDirichletKleinClosed_isClosed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : IsClosed (stabilizerDirichletKleinClosed P w) := by
  have he : stabilizerDirichletKleinClosed P w=⋂g : H,⋂_hg : g • w≠w,
      {u : ℂ | inner ℝ (dirichletCutNormal P w g) u≤dirichletCutThreshold P w g}:=by ext u; simp [stabilizerDirichletKleinClosed]
  rw [he]
  exact isClosed_iInter (fun _=>isClosed_iInter (fun _=>isClosed_le (by fun_prop) continuous_const))

theorem stabilizerDirichletKleinClosed_convex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : Convex ℝ (stabilizerDirichletKleinClosed P w) := by
  have he : stabilizerDirichletKleinClosed P w=⋂g : H,⋂_hg : g • w≠w,
      (innerSL ℝ (dirichletCutNormal P w g)) ⁻¹' Iic (dirichletCutThreshold P w g):=by ext u; simp [stabilizerDirichletKleinClosed]
  rw [he]
  exact convex_iInter (fun g=>convex_iInter (fun _=>(convex_Iic _).linear_preimage (innerSL ℝ (dirichletCutNormal P w
    g)).toLinearMap))

theorem stabilizerDirichlet_klein_image_subset_interior {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) :
    P.kleinCoordinate '' stabilizerDirichletRegion P w⊆interior (stabilizerDirichletKleinClosed P w) := by
  apply interior_maximal _ (P.kleinCoordinate_isOpenEmbedding.isOpenMap _ (stabilizerDirichletRegion_isOpen P w))
  rintro u ⟨z,hz,rfl⟩ g hg
  exact ((dirichletHalfPlane_affine P w z g).mp (hz g hg)).le


theorem stabilizerDirichletCutNormal_regular {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (hg : g • w ≠ w) :
    dirichletCutNormal P w g ≠ 0 ∧ |dirichletCutThreshold P w g| < ‖dirichletCutNormal P w g‖ := by
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricHalfPlane_regular (fun he => hg
    (P.halfPlaneCoordinate.injective he).symm)

theorem stabilizerDirichlet_interior_strict {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)
    {u : ℂ} (hu : u∈interior (stabilizerDirichletKleinClosed P w)) (g : H) (hg : g • w≠w) :
    inner ℝ (dirichletCutNormal P w g) u<dirichletCutThreshold P w g := by
  let f : StrongDual ℝ ℂ:=innerSL ℝ (dirichletCutNormal P w g)
  have hf : f≠0:=by
    intro he
    have hv:=congrArg (fun F : StrongDual ℝ ℂ=>F (dirichletCutNormal P w g)) he
    have hn:=real_inner_self_pos.mpr (stabilizerDirichletCutNormal_regular P w g hg).1
    change inner ℝ (dirichletCutNormal P w g) (dirichletCutNormal P w g)=0 at hv
    linarith
  have hi : u∈interior (f ⁻¹' Iic (dirichletCutThreshold P w g)):=
    interior_mono (show stabilizerDirichletKleinClosed P w⊆f ⁻¹' Iic (dirichletCutThreshold P w g) from fun _ hx=>hx g
      hg) hu
  rw [f.interior_preimage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nielsen_nonzero_functional_surjective f
    hf),interior_Iic] at hi
  exact hi

theorem stabilizerDirichlet_klein_image {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)  :
    P.kleinCoordinate '' stabilizerDirichletRegion P w=
      interior (stabilizerDirichletKleinClosed P w)∩Metric.ball (0 : ℂ) 1 := by
  ext u
  constructor
  · intro hu
    exact ⟨stabilizerDirichlet_klein_image_subset_interior P w hu,
      P.kleinCoordinate_range ▸ mem_range_of_mem_image _ _ hu⟩
  · rintro ⟨hi,hb⟩
    obtain ⟨z,rfl⟩:=P.kleinCoordinate_range ▸ hb
    refine ⟨z,?_,rfl⟩
    intro g hg
    exact (dirichletHalfPlane_affine P w z g).mpr (stabilizerDirichlet_interior_strict P w hi g hg)


theorem closure_stabilizerDirichletRegion_le {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) {z : P.domain.carrier}
    (hz : z ∈ closure (stabilizerDirichletRegion P w)) (g : H) :
    P.hyperbolicDist z w ≤ P.hyperbolicDist z (g • w) := by
  by_cases hg : g • w = w
  · rw [hg]
  · have hc : IsClosed {z | P.hyperbolicDist z w ≤ P.hyperbolicDist z (g • w)} :=
      isClosed_le (P.hyperbolicDist_left_continuous w) (P.hyperbolicDist_left_continuous (g • w))
    have hs : stabilizerDirichletRegion P w ⊆ {z | P.hyperbolicDist z w ≤ P.hyperbolicDist z (g • w)} := by
      intro x hx
      change P.hyperbolicDist x w ≤ P.hyperbolicDist x (g • w)
      exact (hx g hg).le
    exact closure_minimal hs hc hz

theorem closure_stabilizerDirichletRegion {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)  :
    closure (stabilizerDirichletRegion P w)={z | ∀g : H,P.hyperbolicDist z w≤P.hyperbolicDist z (g • w)} := by
  ext z
  constructor
  · intro hz g
    exact closure_stabilizerDirichletRegion_le P w hz g
  · intro hz
    have hzC : P.kleinCoordinate z∈stabilizerDirichletKleinClosed P w:=fun g hg=>(dirichlet_le_affine P w z g).mp (hz g)
    have hInt : (interior (stabilizerDirichletKleinClosed P w)).Nonempty:=
      ⟨P.kleinCoordinate w,stabilizerDirichlet_klein_image_subset_interior P w (mem_image_of_mem _
        (stabilizerDirichletRegion_center_mem P w))⟩
    have hclose : closure (interior (stabilizerDirichletKleinClosed P w))=stabilizerDirichletKleinClosed P w:=
      ((stabilizerDirichletKleinClosed_convex P w).closure_interior_eq_closure_of_nonempty_interior
        hInt).trans (stabilizerDirichletKleinClosed_isClosed P w).closure_eq
    have hzB : P.kleinCoordinate z∈Metric.ball (0 : ℂ) 1:=P.kleinCoordinate_range ▸ mem_range_self z
    have hzI : P.kleinCoordinate z∈closure (interior (stabilizerDirichletKleinClosed P w)∩Metric.ball (0 : ℂ) 1):=
      Metric.isOpen_ball.closure_inter ⟨hclose.symm ▸ hzC,hzB⟩
    rw [←stabilizerDirichlet_klein_image P w] at hzI
    rw [P.kleinCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    exact hzI


theorem stabilizerDirichletRegion_closure_meetsEveryOrbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)  :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H P.domain.carrier (closure (stabilizerDirichletRegion P w)) := by
  intro x
  obtain ⟨g,hg⟩:=P.closest_orbit_representative x w
  refine ⟨g,?_⟩
  rw [closure_stabilizerDirichletRegion P w]
  intro h
  rw [P.hyperbolicDist_inverse_smul]
  simpa only [mul_smul] using hg (h⁻¹*g)


/-- The genuine region is stable exactly under the full original point stabilizer. -/
theorem stabilizerDirichletRegion_stable {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (w : P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsCosetStableRegion (MulAction.stabilizer G w) (stabilizerDirichletRegion P w) := by
  let K := MulAction.stabilizer G w
  have hfixed (h : K) : h.val • w = w := h.property
  have hmap (h : K) : h • stabilizerDirichletRegion P w ⊆ stabilizerDirichletRegion P w := by
    rintro _ ⟨y,hy,rfl⟩ g hg
    have hn : (h.val⁻¹ * g) • w ≠ w := by
      intro he
      apply hg
      have hh := congrArg (fun z => h.val • z) he
      simpa only [mul_smul,smul_inv_smul,hfixed] using hh
    have hi := hy (h.val⁻¹ * g) hn
    have hl : P.hyperbolicDist (h.val • y) w = P.hyperbolicDist y w := by
      calc
        P.hyperbolicDist (h.val • y) w = P.hyperbolicDist (h.val • y) (h.val • w) := by rw [hfixed]
        _ = P.hyperbolicDist y w := P.hyperbolicDist_smul h.val y w
    have hr := P.hyperbolicDist_smul h.val⁻¹ (h.val • y) (g • w)
    rw [inv_smul_smul,←mul_smul] at hr
    change P.hyperbolicDist (h.val • y) w < P.hyperbolicDist (h.val • y) (g • w)
    rw [hl,←hr]
    exact hi
  refine ⟨?_,?_⟩
  · intro h
    apply Subset.antisymm (hmap h)
    intro y hy
    refine ⟨h⁻¹ • y,hmap h⁻¹ ⟨y,hy,rfl⟩,smul_inv_smul h y⟩
  · intro g hg
    have hn : g • w ≠ w := hg
    have hi : g⁻¹ • w ≠ w := by
      intro he
      apply hn
      calc
        g • w = g • (g⁻¹ • w) := congrArg (fun z => g • z) he.symm
        _ = w := smul_inv_smul g w
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ hx
    have h₁ := hx g hn
    have h₂ := hy g⁻¹ hi
    change P.hyperbolicDist (g • y) w < P.hyperbolicDist (g • y) (g • w) at h₁
    rw [P.hyperbolicDist_smul] at h₁
    have he := P.hyperbolicDist_smul g⁻¹ (g • y) w
    rw [inv_smul_smul] at he
    rw [←he] at h₁
    exact h₁.not_ge h₂.le

/-- The full original point stabilizer is genuinely finite, including elliptic centers. -/
theorem UnitDiscFuchsianGroup.point_stabilizer_finite {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (w : P.domain.carrier) : Finite (MulAction.stabilizer G w) := by
  have hf : ((MulAction.stabilizer G w : Subgroup G) : Set G).Finite := by
    apply (P.bounded_orbit_labels w w 0).subset
    intro g hg
    change g • w = w at hg
    change P.hyperbolicDist (g • w) w ≤ 0
    rw [hg,P.hyperbolicDist_self]
  exact hf.to_subtype

theorem stabilizerDirichletRegion_compact_tiles_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)
    (K : Set P.domain.carrier) (hK : IsCompact K) :
    {g : H | (fuchsianDomainTile P (stabilizerDirichletRegion P w) g∩K).Nonempty}.Finite := by
  obtain ⟨r,hr⟩:=P.compact_hyperbolicDist_bound w K hK
  apply (P.bounded_orbit_labels w w (2*r)).subset
  intro g hg
  obtain ⟨x,hx,hxK⟩:=hg
  obtain ⟨u,hu,rfl⟩:=hx
  have huB:=closure_stabilizerDirichletRegion_le P w hu g⁻¹
  rw [P.hyperbolicDist_inverse_smul,inv_inv] at huB
  have hxu:=P.hyperbolicDist_smul g u w
  have ht:=P.hyperbolicDist_triangle w (g • u) (g • w)
  have hrx:=hr (g • u) hxK
  rw [P.hyperbolicDist_comm w (g • u)] at ht
  change P.hyperbolicDist (g • w) w≤2*r
  rw [P.hyperbolicDist_comm]
  linarith


/-- Every genuine convex fundamental polygon for the full point stabilizer yields a true full-group polygon. -/
theorem stabilizerDirichletRegion_intersection_polygon {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (w : P.domain.carrier) (D : Set P.domain.carrier)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (MulAction.stabilizer G w)
      P.domain.carrier P.area D)
    (hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' D)) :
    IsConvexFuchsianPolygon P (D ∩ stabilizerDirichletRegion P w) := by
  let stabilizerDirichletPointFinite : Finite (MulAction.stabilizer G w) := P.point_stabilizer_finite w
  have hl : LocallyFinite (fun h : MulAction.stabilizer G w => h • closure D) := locallyFinite_of_finite _
  have hFD := isFundamentalDomain_inter_of_cosetStable_orbit_cover P (MulAction.stabilizer G
    w) D (stabilizerDirichletRegion P w)
    hD hl hconv (stabilizerDirichletRegion_isOpen P w) (stabilizerDirichletRegion_convex P w)
    (stabilizerDirichletRegion_stable P w) (stabilizerDirichletRegion_closure_meetsEveryOrbit P w)
  refine ⟨⟨hFD,?_⟩,?_⟩
  · intro K hK
    apply (stabilizerDirichletRegion_compact_tiles_finite P w K hK).subset
    rintro g ⟨z,⟨u,hu,he⟩,hzK⟩
    exact ⟨z,⟨u,closure_mono inter_subset_right hu,he⟩,hzK⟩
  · rw [image_inter P.finiteCoordinate.injective]
    intro z hz u hu v hv
    exact ⟨hconv z hz.1 u hu.1 hv,(stabilizerDirichletRegion_convex P w) z hz.2 u hu.2 hv⟩

end
end LowDimensionalTopology.Geometry.Fuchsian
