/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.MetricHalfPlanes
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletOrbits
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenHalfspaces
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane Complex.UnitDisc RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
noncomputable section
local instance dirichletSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance dirichletSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

theorem UnitDiscFuchsianGroup.halfPlaneKleinCoordinate_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (z : P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (P.halfPlaneCoordinate z)=P.kleinCoordinate z := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.finiteCoordinate z)))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate z)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]

theorem UnitDiscFuchsianGroup.halfPlaneCoordinate_cayley {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (z : P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate
      z)=P.finiteCoordinate z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane _

theorem UnitDiscFuchsianGroup.finite_image_halfPlaneCoordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) :
    P.finiteCoordinate '' S=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' (P.halfPlaneCoordinate '' S) := by
  rw [Set.image_image]
  exact Set.image_congr (fun z _=>(P.halfPlaneCoordinate_cayley z).symm)

def dirichletCutNormal {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (g :
      H) : ℂ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricHalfPlaneNormal (P.halfPlaneCoordinate
      w) (P.halfPlaneCoordinate (g • w))

def dirichletCutThreshold {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (g :
      H) : ℝ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricHalfPlaneThreshold (P.halfPlaneCoordinate
      w) (P.halfPlaneCoordinate (g • w))

theorem dirichletHalfPlane_affine {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w z : P.domain.carrier) (g : H) :
    z∈dirichletHalfPlane P w g ↔ inner ℝ (dirichletCutNormal P w g) (P.kleinCoordinate z)<dirichletCutThreshold P w g := by
  change dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)<dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate
    (g • w)) ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_metricHalfPlane_affine,P.halfPlaneKleinCoordinate_eq]
  rfl

theorem dirichlet_le_affine {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w z : P.domain.carrier) (g : H) :
    P.hyperbolicDist z w≤P.hyperbolicDist z (g • w) ↔
      inner ℝ (dirichletCutNormal P w g) (P.kleinCoordinate z)≤dirichletCutThreshold P w g := by
  change dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)≤dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate
    (g • w)) ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_metricHalfPlane_affine_le,P.halfPlaneKleinCoordinate_eq]
  rfl

theorem dirichletBisector_affine {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w z : P.domain.carrier) (g : H) :
    z∈dirichletBisector P w g ↔ inner ℝ (dirichletCutNormal P w g) (P.kleinCoordinate z)=dirichletCutThreshold P w g := by
  change dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)=dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate
    (g • w)) ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_metricHalfPlane_affine_eq,P.halfPlaneKleinCoordinate_eq]
  rfl

theorem dirichletCutNormal_regular {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (g : H) (hg : g≠1) :
    dirichletCutNormal P w g≠0 ∧ |dirichletCutThreshold P w g|<‖dirichletCutNormal P w g‖ := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricHalfPlane_regular
  intro he
  exact hg (hw g (P.halfPlaneCoordinate.injective he).symm)

theorem dirichletHalfPlane_convex {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (g : H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' dirichletHalfPlane P w g) := by
  rw [P.finite_image_halfPlaneCoordinate]
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mp
  have he : P.halfPlaneCoordinate '' dirichletHalfPlane P w g=
      {z : ℍ | dist z (P.halfPlaneCoordinate w)<dist z (P.halfPlaneCoordinate (g • w))}:=by
    ext z
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro hz
      change dist z (P.halfPlaneCoordinate w)<dist z (P.halfPlaneCoordinate (g • w)) at hz
      refine ⟨P.halfPlaneCoordinate.symm z,?_,P.halfPlaneCoordinate.apply_symm_apply z⟩
      change dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate
        w)<dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate (g • w))
      simpa only [P.halfPlaneCoordinate.apply_symm_apply] using hz
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_closer_halfPlane_convex _ _

theorem dirichletDomain_convex {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' dirichletDomain P w) := by
  have he : P.finiteCoordinate '' dirichletDomain P w=
      ⋂g : H,⋂hg : g≠1,P.finiteCoordinate '' dirichletHalfPlane P w g:=by
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


/-- Closed affine comparison intersection in the ambient Klein plane. -/
def dirichletKleinClosed {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : Set ℂ :=
  {u | ∀g : H,g≠1 → inner ℝ (dirichletCutNormal P w g) u≤dirichletCutThreshold P w g}

theorem dirichletKleinClosed_isClosed {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : IsClosed (dirichletKleinClosed P w) := by
  have he : dirichletKleinClosed P w=⋂g : H,⋂_hg : g≠1,
      {u : ℂ | inner ℝ (dirichletCutNormal P w g) u≤dirichletCutThreshold P w g}:=by ext u; simp [dirichletKleinClosed]
  rw [he]
  exact isClosed_iInter (fun _=>isClosed_iInter (fun _=>isClosed_le (by fun_prop) continuous_const))

theorem dirichletKleinClosed_convex {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : Convex ℝ (dirichletKleinClosed P w) := by
  have he : dirichletKleinClosed P w=⋂g : H,⋂_hg : g≠1,
      (innerSL ℝ (dirichletCutNormal P w g)) ⁻¹' Iic (dirichletCutThreshold P w g):=by ext u; simp [dirichletKleinClosed]
  rw [he]
  exact convex_iInter (fun g=>convex_iInter (fun _=>(convex_Iic _).linear_preimage (innerSL ℝ (dirichletCutNormal P w
    g)).toLinearMap))

theorem UnitDiscFuchsianGroup.kleinCoordinate_range {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : range P.kleinCoordinate=Metric.ball (0 : ℂ) 1 := by
  change range (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ∘ P.finiteCoordinate)=_
  rw [range_comp, P.finiteCoordinate.surjective.range_eq, image_univ,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]

theorem dirichlet_klein_image_subset_interior {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) :
    P.kleinCoordinate '' dirichletDomain P w⊆interior (dirichletKleinClosed P w) := by
  apply interior_maximal _ (P.kleinCoordinate_isOpenEmbedding.isOpenMap _ (dirichletDomain_isOpen P w))
  rintro u ⟨z,hz,rfl⟩ g hg
  exact ((dirichletHalfPlane_affine P w z g).mp (hz g hg)).le

theorem dirichlet_interior_strict {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    {u : ℂ} (hu : u∈interior (dirichletKleinClosed P w)) (g : H) (hg : g≠1) :
    inner ℝ (dirichletCutNormal P w g) u<dirichletCutThreshold P w g := by
  let f : StrongDual ℝ ℂ:=innerSL ℝ (dirichletCutNormal P w g)
  have hf : f≠0:=by
    intro he
    have hv:=congrArg (fun F : StrongDual ℝ ℂ=>F (dirichletCutNormal P w g)) he
    have hn:=real_inner_self_pos.mpr (dirichletCutNormal_regular P w hw g hg).1
    change inner ℝ (dirichletCutNormal P w g) (dirichletCutNormal P w g)=0 at hv
    linarith
  have hi : u∈interior (f ⁻¹' Iic (dirichletCutThreshold P w g)):=
    interior_mono (show dirichletKleinClosed P w⊆f ⁻¹' Iic (dirichletCutThreshold P w g) from fun _ hx=>hx g hg) hu
  rw [f.interior_preimage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nielsen_nonzero_functional_surjective f
    hf),interior_Iic] at hi
  exact hi

theorem dirichlet_klein_image {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    P.kleinCoordinate '' dirichletDomain P w=
      interior (dirichletKleinClosed P w)∩Metric.ball (0 : ℂ) 1 := by
  ext u
  constructor
  · intro hu
    exact ⟨dirichlet_klein_image_subset_interior P w hu,
      P.kleinCoordinate_range ▸ mem_range_of_mem_image _ _ hu⟩
  · rintro ⟨hi,hb⟩
    obtain ⟨z,rfl⟩:=P.kleinCoordinate_range ▸ hb
    refine ⟨z,?_,rfl⟩
    intro g hg
    exact (dirichletHalfPlane_affine P w z g).mpr (dirichlet_interior_strict P w hw hi g hg)

theorem closure_dirichletDomain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    closure (dirichletDomain P w)={z | ∀g : H,P.hyperbolicDist z w≤P.hyperbolicDist z (g • w)} := by
  ext z
  constructor
  · intro hz g
    exact closure_dirichletDomain_le P w hz g
  · intro hz
    have hzC : P.kleinCoordinate z∈dirichletKleinClosed P w:=fun g hg=>(dirichlet_le_affine P w z g).mp (hz g)
    have hInt : (interior (dirichletKleinClosed P w)).Nonempty:=
      ⟨P.kleinCoordinate w,dirichlet_klein_image_subset_interior P w (mem_image_of_mem _ (dirichletDomain_center_mem P w
        hw))⟩
    have hclose : closure (interior (dirichletKleinClosed P w))=dirichletKleinClosed P w:=
      ((dirichletKleinClosed_convex P w).closure_interior_eq_closure_of_nonempty_interior
        hInt).trans (dirichletKleinClosed_isClosed P w).closure_eq
    have hzB : P.kleinCoordinate z∈Metric.ball (0 : ℂ) 1:=P.kleinCoordinate_range ▸ mem_range_self z
    have hzI : P.kleinCoordinate z∈closure (interior (dirichletKleinClosed P w)∩Metric.ball (0 : ℂ) 1):=
      Metric.isOpen_ball.closure_inter ⟨hclose.symm ▸ hzC,hzB⟩
    rw [←dirichlet_klein_image P w hw] at hzI
    rw [P.kleinCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    exact hzI


/-- Choice of one actual point per orbit, preserving a prescribed unique interior set. -/
theorem exists_fundamentalSet_between {G X : Type*} [Group G] [MulAction G X]
    (D C : Set X) (hDC : D⊆C) (hC : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit G X C)
    (hD : ∀x∈D,∀y∈D,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X
      x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X y→x=y) :
    ∃F : Set X,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet G X F ∧ D⊆F ∧ F⊆C := by
  classical
  have hc (q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient G X) : ∃y∈C,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X y=q:=by
    obtain ⟨g,hg⟩:=hC q.out
    exact ⟨g • q.out,hg,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul G X g
      q.out).trans (Quotient.out_eq q)⟩
  let r : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient G X→X:=fun q=>
    if h : ∃y∈D,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X y=q then h.choose else (hc q).choose
  have hrD (q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient G X) (hq :
    ∃y∈D,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X y=q) :
      r q∈D ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X (r q)=q:=by
    simp only [r,dite_eq_left hq]
    exact hq.choose_spec
  have hr (q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient G X) : r q∈C ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X (r q)=q:=by
    by_cases hq : ∃y∈D,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X y=q
    · exact ⟨hDC (hrD q hq).1,(hrD q hq).2⟩
    · simpa only [r,dite_eq_right hq] using (hc q).choose_spec
  refine ⟨range r,?_,?_,?_⟩
  · intro x
    refine ⟨r (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X x),⟨mem_range_self _,(hr
      _).2⟩,?_⟩
    rintro y ⟨⟨q,rfl⟩,hy⟩
    exact congrArg r ((hr q).2.symm.trans hy)
  · intro x hx
    have he : r (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X x)=x:=
      hD _ (hrD _ ⟨x,hx,rfl⟩).1 x hx (hrD _ ⟨x,hx,rfl⟩).2
    exact ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X x,he⟩
  · rintro y ⟨q,rfl⟩
    exact (hr q).1

theorem dirichletDomain_orbit_unique {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) {x y : P.domain.carrier}
    (hx : x∈dirichletDomain P w) (hy : y∈dirichletDomain P w)
    (hxy : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier y) : x=y := by
  obtain ⟨g,hg⟩:=(Quotient.exact hxy : MulAction.orbitRel H P.domain.carrier x y)
  change g • y=x at hg
  by_cases he : g=1
  · simpa only [he,one_smul] using hg.symm
  · have hd:=dirichlet_closed_orbit_equal_distance P w y g (subset_closure hy) (hg.symm ▸ subset_closure hx)
    have hh:=hy g⁻¹ (inv_ne_one.mpr he)
    change P.hyperbolicDist y w<P.hyperbolicDist y (g⁻¹ • w) at hh
    rw [P.hyperbolicDist_inverse_smul,inv_inv] at hh
    exact (lt_irrefl _ (hd ▸ hh)).elim

theorem dirichletDomain_closure_meetsEveryOrbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H P.domain.carrier (closure (dirichletDomain P w)) := by
  intro x
  obtain ⟨g,hg⟩:=P.closest_orbit_representative x w
  refine ⟨g,?_⟩
  rw [closure_dirichletDomain P w hw]
  intro h
  rw [P.hyperbolicDist_inverse_smul]
  simpa only [mul_smul] using hg (h⁻¹*g)

theorem dirichletDomain_fundamentalSet {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    ∃F : Set P.domain.carrier,IsFuchsianFundamentalSet P F ∧
      dirichletDomain P w⊆F ∧ F⊆closure (dirichletDomain P w) :=
  exists_fundamentalSet_between _ _ subset_closure
    (dirichletDomain_closure_meetsEveryOrbit P w hw)
    (fun _ hx _ hy hxy=>dirichletDomain_orbit_unique P w hx hy hxy)

theorem dirichletDomain_compact_tiles_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier)
    (K : Set P.domain.carrier) (hK : IsCompact K) :
    {g : H | (fuchsianDomainTile P (dirichletDomain P w) g∩K).Nonempty}.Finite := by
  obtain ⟨r,hr⟩:=P.compact_hyperbolicDist_bound w K hK
  apply (P.bounded_orbit_labels w w (2*r)).subset
  intro g hg
  obtain ⟨x,hx,hxK⟩:=hg
  obtain ⟨u,hu,rfl⟩:=hx
  have huB:=closure_dirichletDomain_le P w hu g⁻¹
  rw [P.hyperbolicDist_inverse_smul,inv_inv] at huB
  have hxu:=P.hyperbolicDist_smul g u w
  have ht:=P.hyperbolicDist_triangle w (g • u) (g • w)
  have hrx:=hr (g • u) hxK
  rw [P.hyperbolicDist_comm w (g • u)] at ht
  change P.hyperbolicDist (g • w) w≤2*r
  rw [P.hyperbolicDist_comm]
  linarith

theorem dirichletDomain_frontier_subset_bisectors {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) :
    frontier (dirichletDomain P w)⊆⋃g : {g : H // g≠1},dirichletBisector P w g.val := by
  intro z hz
  have hc:=frontier_subset_closure hz
  have hn : z∉dirichletDomain P w:=by
    simpa only [(dirichletDomain_isOpen P w).interior_eq] using hz.2
  have hex : ∃g : H,g≠1 ∧ ¬ z∈dirichletHalfPlane P w g:=by
    by_contra he
    push Not at he
    exact hn (fun g hg=>he g hg)
  obtain ⟨g,hg,hzg⟩:=hex
  refine mem_iUnion.mpr ⟨⟨g,hg⟩,?_⟩
  change P.hyperbolicDist z w=P.hyperbolicDist z (g • w)
  change ¬P.hyperbolicDist z w<P.hyperbolicDist z (g • w) at hzg
  exact le_antisymm (closure_dirichletDomain_le P w hc g) (le_of_not_gt hzg)


theorem UnitDiscFuchsianGroup.area_eq_halfPlane_volume {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) (hS : MeasurableSet S) :
    P.area S=volume (P.halfPlaneCoordinate '' S) := by
  rw [P.area_apply S hS,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea_eq_halfPlane_volume _
    (P.finiteCoordinate.measurableEmbedding.measurableSet_image.mpr hS),image_image]
  rfl

theorem dirichletBisector_halfPlane_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) :
    P.halfPlaneCoordinate '' dirichletBisector P w g=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate (g • w)) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hz
    change dist z (P.halfPlaneCoordinate w)=dist z (P.halfPlaneCoordinate (g • w)) at hz
    refine ⟨P.halfPlaneCoordinate.symm z,?_,P.halfPlaneCoordinate.apply_symm_apply z⟩
    change dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate w)=
      dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate (g • w))
    simpa only [P.halfPlaneCoordinate.apply_symm_apply] using hz

theorem dirichletHalfPlane_halfPlane_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) :
    P.halfPlaneCoordinate '' dirichletHalfPlane P w g=
      {z : ℍ | dist z (P.halfPlaneCoordinate w)<dist z (P.halfPlaneCoordinate (g • w))} := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hz
    change dist z (P.halfPlaneCoordinate w)<dist z (P.halfPlaneCoordinate (g • w)) at hz
    refine ⟨P.halfPlaneCoordinate.symm z,?_,P.halfPlaneCoordinate.apply_symm_apply z⟩
    change dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate w)<
      dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate (g • w))
    simpa only [P.halfPlaneCoordinate.apply_symm_apply] using hz

theorem dirichletBisector_geodesic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (g : H) (hg : g≠1) : ∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,
    L.carrier=P.halfPlaneCoordinate '' dirichletBisector P w g ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane L (P.halfPlaneCoordinate w)=P.halfPlaneCoordinate '' dirichletHalfPlane P w g := by
  have hab : P.halfPlaneCoordinate w≠P.halfPlaneCoordinate (g • w):=by
    intro he
    exact hg (hw g (P.halfPlaneCoordinate.injective he).symm)
  obtain ⟨L,hLB,hLH⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_closer_halfPlane hab
  exact ⟨L,hLB.trans (dirichletBisector_halfPlane_image P w g).symm,
    hLH.symm.trans (dirichletHalfPlane_halfPlane_image P w g).symm⟩

theorem dirichletBisector_area_zero {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (g : H) (hg : g≠1) : P.area (dirichletBisector P w g)=0 := by
  obtain ⟨L,hL,_⟩:=dirichletBisector_geodesic P w hw g hg
  rw [P.area_eq_halfPlane_volume _ (dirichletBisector_isClosed P w g).measurableSet,←hL]
  exact L.volume_zero

theorem dirichletDomain_frontier_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    P.area (frontier (dirichletDomain P w))=0 := by
  let : Countable H:=P.countable
  exact measure_mono_null (dirichletDomain_frontier_subset_bisectors P w)
    (measure_iUnion_null (fun g : {g : H // g≠1}=>dirichletBisector_area_zero P w hw g.val g.property))

theorem dirichletDomain_isConnected {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    IsConnected (dirichletDomain P w) := by
  exact ⟨dirichletDomain_nonempty P w hw,
    P.finiteCoordinate.isEmbedding.isInducing.isPreconnected_image.mp (dirichletDomain_convex P w).isPreconnected⟩

theorem dirichletDomain_fundamental {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    IsFuchsianFundamentalDomain P (dirichletDomain P w) := by
  apply (isFuchsianFundamentalDomain_iff P _).mpr
  exact ⟨dirichletDomain_isOpen P w,dirichletDomain_isConnected P w hw,
    dirichletDomain_fundamentalSet P w hw,dirichletDomain_frontier_area_zero P w hw⟩

theorem dirichletDomain_locallyFinite {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    IsLocallyFiniteFuchsianDomain P (dirichletDomain P w) :=
  ⟨dirichletDomain_fundamental P w hw,dirichletDomain_compact_tiles_finite P w⟩

/-- For the original actual Fuchsian action and genuine area. -/
theorem dirichletDomain_isConvexFuchsianPolygon {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    IsConvexFuchsianPolygon P (dirichletDomain P w) :=
  ⟨dirichletDomain_locallyFinite P w hw,dirichletDomain_convex P w⟩

end
end LowDimensionalTopology.Geometry.Fuchsian
