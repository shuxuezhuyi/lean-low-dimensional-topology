module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.PolygonCompactCircleCores
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSideInteriors
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance circlePairSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance circlePairSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- At a genuine nonvertex polygon boundary point, the nonidentity boundary mate is unique. -/
theorem polygon_nonvertex_boundary_mate_unique
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier}
    (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    ∃! g : H, g ≠ 1 ∧ g • x ∈ frontier D := by
  obtain ⟨g,hg,hgx⟩ := hD.boundary_mate hx
  obtain ⟨k,_hk,hunique⟩ := hD.nonvertex_incident_unique hx hnv
  have hgk : g⁻¹ = k := hunique g⁻¹ ⟨inv_ne_one.mpr hg,
    g • x,frontier_subset_closure hgx,inv_smul_smul g x⟩
  refine ⟨g,⟨hg,hgx⟩,?_⟩
  rintro h ⟨hh,hhx⟩
  have hhk : h⁻¹ = k := hunique h⁻¹ ⟨inv_ne_one.mpr hh,
    h • x,frontier_subset_closure hhx,inv_smul_smul h x⟩
  exact inv_injective (hhk.trans hgk.symm)

/-- The literal cut points of the genuine Dirichlet boundary by a genuine metric circle. -/
def dirichletCircleCuts {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) : Set P.domain.carrier :=
  frontier (dirichletDomain P w) ∩ {x | P.hyperbolicDist w x = R}

/-- The actual Dirichlet circle cut-point set is finite. -/
theorem dirichletCircleCuts_finite {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ) :
    (dirichletCircleCuts P w R).Finite :=
  fuchsian_polygon_frontier_hyperbolic_circle_inter_finite (dirichletDomain_isConvexFuchsianPolygon P w hw) w R

/-- True original-group boundary mates of a Dirichlet circle cut point remain on the same circle. -/
theorem dirichletCircleCut_mate_mem {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ)
    {x : P.domain.carrier} (hx : x ∈ dirichletCircleCuts P w R)
    (g : H) (hgx : g • x ∈ frontier (dirichletDomain P w)) :
    g • x ∈ dirichletCircleCuts P w R := by
  refine ⟨hgx,?_⟩
  have he := dirichlet_closed_orbit_equal_distance P w x g
    (frontier_subset_closure hx.1) (frontier_subset_closure hgx)
  change P.hyperbolicDist w (g • x) = R
  rw [P.hyperbolicDist_comm,←he,P.hyperbolicDist_comm]
  exact hx.2

/-- The genuine Dirichlet cut-point mate is unique at every actual nonvertex cut point. -/
theorem dirichletCircleCut_mate_existsUnique {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    {x : P.domain.carrier} (hx : x ∈ dirichletCircleCuts P w R)
    (hnv : ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    ∃! g : H, g ≠ 1 ∧ g • x ∈ dirichletCircleCuts P w R := by
  obtain ⟨g,⟨hg,hgx⟩,hunique⟩ := polygon_nonvertex_boundary_mate_unique
    (dirichletDomain_isConvexFuchsianPolygon P w hw) hx.1 hnv
  exact ⟨g,⟨hg,dirichletCircleCut_mate_mem P w R hx g hgx⟩,
    fun h hh => hunique h ⟨hh.1,hh.2.1⟩⟩

/-- Arbitrarily large true polygon circle radii avoid both actual vertices and all actual elliptic fixed points. -/
theorem exists_polygon_radius_avoiding_vertices_and_elliptic
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (w : P.domain.carrier) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
      ¬ IsFuchsianPolygonVertex P D x ∧ IsDirichletCenter P x := by
  let A : Set P.domain.carrier := {x | IsFuchsianPolygonVertex P D x} ∪ fuchsianEllipticPoints P
  have hA : A.Countable := (fuchsianPolygonVertices_countable P D).union (fuchsianEllipticPoints_countable P)
  have hB : ((fun x => P.hyperbolicDist w x) '' A).Countable := hA.image _
  obtain ⟨R,hR,hRB⟩ := (hB.dense_compl ℝ).inter_open_nonempty (Ioi R₀) isOpen_Ioi nonempty_Ioi
  refine ⟨R,hR,?_⟩
  intro x hx
  have hxA : x ∉ A := fun hxa => hRB ⟨x,hxa,hx⟩
  refine ⟨fun hv => hxA (Or.inl hv),?_⟩
  by_contra hc
  exact hxA (Or.inr hc)

/-- The selected actual original group element pairing a nonvertex Dirichlet cut point. -/
def dirichletCircleMateElement {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (x : dirichletCircleCuts P w R) : H :=
  (dirichletCircleCut_mate_existsUnique P w hw R x.property (hReg x.val x.property)).choose

/-- The selected cut-point pairing element is genuinely nonidentity and carries the actual point to an actual cut point. -/
theorem dirichletCircleMateElement_spec {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (x : dirichletCircleCuts P w R) :
    dirichletCircleMateElement P w hw R hReg x ≠ 1 ∧
      dirichletCircleMateElement P w hw R hReg x • x.val ∈ dirichletCircleCuts P w R :=
  (dirichletCircleCut_mate_existsUnique P w hw R x.property (hReg x.val x.property)).choose_spec.1

/-- The genuine cut-point mate, in the literal finite original cut-point set. -/
def dirichletCircleMate {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    dirichletCircleCuts P w R → dirichletCircleCuts P w R :=
  fun x => ⟨dirichletCircleMateElement P w hw R hReg x • x.val,
    (dirichletCircleMateElement_spec P w hw R hReg x).2⟩

/-- The two genuine original-group cut-point pairings are inverse to one another. -/
theorem dirichletCircleMate_involutive {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    Function.Involutive (dirichletCircleMate P w hw R hReg) := by
  intro x
  let g := dirichletCircleMateElement P w hw R hReg x
  let y := dirichletCircleMate P w hw R hReg x
  have hg : g ≠ 1 := (dirichletCircleMateElement_spec P w hw R hReg x).1
  have hgy : g⁻¹ • y.val = x.val := inv_smul_smul g x.val
  have huniq := (dirichletCircleCut_mate_existsUnique P w hw R y.property
    (hReg y.val y.property)).choose_spec.2
  have he : g⁻¹ = dirichletCircleMateElement P w hw R hReg y :=
    huniq g⁻¹ ⟨inv_ne_one.mpr hg,by rw [hgy]; exact x.property⟩
  apply Subtype.ext
  change dirichletCircleMateElement P w hw R hReg y • y.val = x.val
  rw [←he,hgy]

/-- Avoiding the actual elliptic fixed points makes the actual finite cut-point pairing fixed-point-free. -/
theorem dirichletCircleMate_ne_self {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (hFree : ∀ x ∈ dirichletCircleCuts P w R, IsDirichletCenter P x)
    (x : dirichletCircleCuts P w R) : dirichletCircleMate P w hw R hReg x ≠ x := by
  intro he
  have hf : dirichletCircleMateElement P w hw R hReg x • x.val = x.val := congrArg Subtype.val he
  exact (dirichletCircleMateElement_spec P w hw R hReg x).1 (hFree x.val x.property _ hf)


/-- The actual cut-point boundary pairing bundled as a permutation of the literal cut set. -/
def dirichletCircleCutPairing {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    Equiv.Perm (dirichletCircleCuts P w R) :=
  (dirichletCircleMate_involutive P w hw R hReg).toPerm (dirichletCircleMate P w hw R hReg)

/-- Arbitrarily large genuine Dirichlet metric circles carry a finite, fixed-point-free
involutive pairing of their literal boundary cut points by unique actual original group elements. -/
theorem exists_dirichlet_circle_cut_pairing {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧ (dirichletCircleCuts P w R).Finite ∧
      ∃ e : Equiv.Perm (dirichletCircleCuts P w R), Function.Involutive e ∧
        (∀ x, e x ≠ x) ∧ ∀ x, ∃! g : H, g ≠ 1 ∧ g • x.val = (e x).val := by
  obtain ⟨R,hR,havoid⟩ := exists_polygon_radius_avoiding_vertices_and_elliptic P
    (dirichletDomain P w) w (max R₀ 0)
  have hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬ IsFuchsianPolygonVertex P (dirichletDomain P w) x := fun x hx => (havoid x hx.2).1
  have hFree : ∀ x ∈ dirichletCircleCuts P w R, IsDirichletCenter P x :=
    fun x hx => (havoid x hx.2).2
  let e := dirichletCircleCutPairing P w hw R hReg
  refine ⟨R,(le_max_left _ _).trans_lt hR,(le_max_right _ _).trans_lt hR,
    dirichletCircleCuts_finite P w hw R,e,dirichletCircleMate_involutive P w hw R hReg,
    dirichletCircleMate_ne_self P w hw R hReg hFree,?_⟩
  intro x
  let g := dirichletCircleMateElement P w hw R hReg x
  refine ⟨g,⟨(dirichletCircleMateElement_spec P w hw R hReg x).1,rfl⟩,?_⟩
  intro h hh
  have hmem : h • x.val ∈ dirichletCircleCuts P w R := hh.2.symm ▸ (e x).property
  exact (dirichletCircleCut_mate_existsUnique P w hw R x.property
    (hReg x.val x.property)).choose_spec.2 h ⟨hh.1,hmem⟩

end LowDimensionalTopology.Geometry.Fuchsian
