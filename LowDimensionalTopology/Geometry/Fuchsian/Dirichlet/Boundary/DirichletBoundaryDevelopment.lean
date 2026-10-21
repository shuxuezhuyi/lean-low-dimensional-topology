module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletArcDevelopment
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.AlternatingArcCycles
public import Mathlib.Dynamics.PeriodicPts.Defs
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Pointwise unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The genuine invertible endpoint motion records both the original endpoint and
its actual accumulated tile, retaining information absent from a finite cut permutation. -/
def endpointSkewPermutation {G X : Type*} [Group G] (r : Equiv.Perm X) (c : X → G) :
    Equiv.Perm (G × X) where
  toFun z := (z.1*c z.2,r z.2)
  invFun z := (z.1*(c (r.symm z.2))⁻¹,r.symm z.2)
  left_inv z := by
    apply Prod.ext
    · simp only [r.symm_apply_apply,mul_inv_cancel_right]
    · exact r.symm_apply_apply z.2
  right_inv z := by
    apply Prod.ext
    · simp only [mul_assoc,inv_mul_cancel,mul_one]
    · exact r.apply_symm_apply z.2

/-- The original endpoint component is exactly the true iterated finite endpoint motion. -/
theorem endpointSkewPermutation_pow_snd {G X : Type*} [Group G]
    (r : Equiv.Perm X) (c : X → G) (n : ℕ) (g : G) (x : X) :
    (((endpointSkewPermutation r c)^n) (g,x)).2 = (r^n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      change r ((((endpointSkewPermutation r c)^n) (g,x)).2) = (r^(n+1)) x
      rw [ih,pow_succ',Equiv.Perm.mul_apply]

/-- Every true endpoint iterate commutes with actual left translation of the tile. -/
theorem endpointSkewPermutation_pow_left_mul {G X : Type*} [Group G]
    (r : Equiv.Perm X) (c : X → G) (n : ℕ) (g h : G) (x : X) :
    ((endpointSkewPermutation r c)^n) (g*h,x) =
      (g*(((endpointSkewPermutation r c)^n) (h,x)).1,
        (((endpointSkewPermutation r c)^n) (h,x)).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,ih]
      apply Prod.ext
      · change (g*_) * _ = g*(_*_)
        exact mul_assoc _ _ _
      · rfl

/-- The actual path-development tile recurrence agrees exactly with the genuine
invertible skew endpoint permutation, not merely its projected finite permutation. -/
theorem endpointSkewPermutation_development_state {G X : Type*} [Group G]
    (a b : Equiv.Perm X) (t : X → G) (n : ℕ) (x : X) :
    ((endpointSkewPermutation (a*b) (fun z => (t (b z))⁻¹))^n) (1,x) =
      (pathDevelopmentTransform (fun m => t (b (((a*b)^m) x))) n,((a*b)^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,ih]
      apply Prod.ext
      · rfl
      · change (a*b) (((a*b)^n) x) = ((a*b)^(n+1)) x
        rw [pow_succ']
        rfl

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Any actual nonidentity mate specification on genuine nonvertex Dirichlet cuts
is forced to be the original canonical Dirichlet pairing. -/
theorem dirichlet_pairing_eq_of_actual_mate_spec
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (a : Equiv.Perm (dirichletCircleCuts P w R))
    (ha : ∀ x, ∃ k : H, k ≠ 1 ∧ k • x.val = (a x).val) :
    a = dirichletCircleCutPairing P w hw R hReg := by
  apply Equiv.ext
  intro x
  obtain ⟨k,hkne,hk⟩ := ha x
  have hmem : k • x.val ∈ dirichletCircleCuts P w R := hk.symm ▸ (a x).property
  have he : k = dirichletCircleMateElement P w hw R hReg x :=
    (dirichletCircleCut_mate_existsUnique P w hw R x.property (hReg x.val x.property)).choose_spec.2
      k ⟨hkne,hmem⟩
  apply Subtype.ext
  change (a x).val = dirichletCircleMateElement P w hw R hReg x • x.val
  rw [←he,hk]

/-- Equality of actual developed starting points is precisely equality of the full
invertible endpoint states, including the genuine accumulated original group element. -/
theorem dirichlet_endpointSkewPermutation_start_eq_iff
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (a b : Equiv.Perm (dirichletCircleCuts P w R))
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x)
    (hA : a = dirichletCircleCutPairing P w hw R hReg)
    (t : dirichletCircleCuts P w R → H) (m n : ℕ) (x : dirichletCircleCuts P w R) :
    let F := endpointSkewPermutation (a*b) (fun z => (t (b z))⁻¹)
    (((F^m) (1,x)).1 • (((F^m) (1,x)).2).val =
      ((F^n) (1,x)).1 • (((F^n) (1,x)).2).val) ↔ (F^m) (1,x) = (F^n) (1,x) := by
  dsimp only
  constructor
  · intro he
    have hm := endpointSkewPermutation_pow_snd (a*b) (fun z => (t (b z))⁻¹) m 1 x
    have hn := endpointSkewPermutation_pow_snd (a*b) (fun z => (t (b z))⁻¹) n 1 x
    rw [hm,hn] at he
    obtain ⟨hg,hx⟩ := dirichlet_alternating_translated_starts_unique P w hw R hReg
      a b ha hb haNe hbNe hA m n x _ _ he
    apply Prod.ext hg
    rw [hm,hn,hx]
  · intro he
    rw [he]

/-- The actual open part of the canonical genuine metric-circle chart inside the original Dirichlet polygon. -/
def dirichletCircleRegion {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) : Set Circle :=
  (fun u => (fuchsianMetricCircleHomeomorph P w R hR u).val) ⁻¹' dirichletDomain P w

/-- A genuine regular original Dirichlet circle, retaining the actual geometric
conditions needed for global path separation rather than discarding them after finite pairing. -/
structure RegularDirichletCircleData {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) where
  radius : ℝ
  radius_pos : 0 < radius
  orbit_neighborhood_open : IsOpen (fuchsianOrbitBallUnion P w radius)
  orbit_neighborhood_connected : IsConnected (fuchsianOrbitBallUnion P w radius)
  cuts_regular : ∀ x ∈ dirichletCircleCuts P w radius,
    ¬IsFuchsianPolygonVertex P (dirichletDomain P w) x
  cuts_free : ∀ x ∈ dirichletCircleCuts P w radius, IsDirichletCenter P x
  exterior : Circle
  exterior_not_closure : exterior ∉ closure (dirichletCircleRegion P w radius radius_pos)
  closed_circle_eq : closure (dirichletDomain P w ∩ {x | P.hyperbolicDist w x = radius}) =
    closure (dirichletDomain P w) ∩ {x | P.hyperbolicDist w x = radius}
  unique_incidence : ∀ p ∈ frontier (dirichletCircleRegion P w radius radius_pos), ∃! V : Set Circle,
    V ∈ ((fun x => connectedComponentIn (dirichletCircleRegion P w radius radius_pos) x) ''
      dirichletCircleRegion P w radius radius_pos) ∧ p ∈ closure V

/-- Genuine finite generation gives cofinally large actual regular Dirichlet circles
with the full original open connected orbit neighborhood, actual nonvertex free cuts,
a true exterior neighborhood, and unique actual component incidence at each frontier point. -/
theorem finitelyGenerated_regular_dirichlet_circle_data
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (hFG :
      H.FG)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ d : RegularDirichletCircleData P w, R₀ < d.radius := by
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  obtain ⟨R₁,_hR₁,hconn⟩ := finitelyGenerated_cofinal_orbitBallUnions_connected P hFG w hw
  obtain ⟨R,hbig,hR,havoid,hside,hclosed,_⟩ := exists_polygon_circle_finite_transverse_arc_boundary
    hD w (max R₀ (max R₁ (P.hyperbolicDist w (g • w))))
  have hc := hconn R ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hbig))
  have hz : g • w ∉ closure (dirichletDomain P w) := fun hh =>
    disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image_closure hg)
      (smul_mem_smul_set (dirichletDomain_center_mem P w hw)) hh
  obtain ⟨z,hzR,hzD⟩ := fuchsian_polygon_large_circle_exterior hD w (g • w)
    (dirichletDomain_center_mem P w hw) hz R
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hbig))
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let f : Circle → P.domain.carrier := fun u => (e u).val
  let U := dirichletCircleRegion P w R hR
  let u := e.symm ⟨z,hzR⟩
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hfu : f u = z := congrArg Subtype.val (e.apply_symm_apply ⟨z,hzR⟩)
  have hu : u ∉ closure U := by
    intro hh
    exact hzD (hfu ▸ hf.closure_preimage_subset (dirichletDomain P w) hh)
  have hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V := by
    intro p hp
    apply fuchsian_circle_one_sided_unique_chart_component P w R hR e p
    exact hside (f p) (hf.frontier_preimage_subset (dirichletDomain P w) hp) (e p).property
  refine ⟨{ radius := R
            radius_pos := hR
            orbit_neighborhood_open := hc.1
            orbit_neighborhood_connected := hc.2
            cuts_regular := fun x hx => (havoid x hx.2).1
            cuts_free := fun x hx => (havoid x hx.2).2
            exterior := u
            exterior_not_closure := hu
            closed_circle_eq := hclosed
            unique_incidence := hinc },?_⟩
  exact (le_max_left _ _).trans_lt hbig

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

theorem region_isOpen : IsOpen (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius
  d.radius_pos) :=
  (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_isOpen P w).preimage
    (continuous_subtype_val.comp (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w
      d.radius d.radius_pos).continuous)

/-- The original-coordinate preserving genuine circle-cut equivalence of the regular data. -/
def cutEquiv (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) :
    ↥(frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius
      d.radius_pos)) ≃ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianCircleFrontierCutEquiv (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w hw) w d.radius
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w d.radius
      d.radius_pos) d.closed_circle_eq

/-- The genuine reversal of actual component endpoints on the actual chart circle. -/
def circleReversal : Equiv.Perm (frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w
  d.radius d.radius_pos)) :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.circleFrontierArcReversal d.region_isOpen d.exterior d.exterior_not_closure d.unique_incidence

/-- The same true component-arc reversal on the literal original cut set. -/
def arcReversal (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P
  w) : Equiv.Perm (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :=
  (d.cutEquiv hw).permCongr d.circleReversal

theorem arcReversal_involutive (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) : Function.Involutive (d.arcReversal hw) := by
  let E := d.cutEquiv hw
  let B := d.circleReversal
  have hBi : Function.Involutive B :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.circleFrontierArcMate_involutive d.region_isOpen d.exterior d.exterior_not_closure d.unique_incidence
  intro x
  change E (B (E.symm (E (B (E.symm x))))) = x
  rw [E.symm_apply_apply,hBi,E.apply_symm_apply]

theorem arcReversal_ne_self (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.arcReversal hw x ≠ x := by
  let E := d.cutEquiv hw
  let B := d.circleReversal
  have hBne : ∀ p, B p ≠ p :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.circleFrontierArcMate_ne_self d.region_isOpen d.exterior d.exterior_not_closure d.unique_incidence
  intro he
  apply hBne (E.symm x)
  have hh := congrArg E.symm he
  change E.symm (E (B (E.symm x))) = E.symm x at hh
  rwa [E.symm_apply_apply] at hh

theorem arcReversal_neighbor (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.circleArcEndpointNeighbor (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius d.radius_pos)
      ((d.cutEquiv hw).symm x).val ((d.cutEquiv hw).symm (d.arcReversal hw x)).val := by
  let E := d.cutEquiv hw
  let B := d.circleReversal
  change _root_.LowDimensionalTopology.Geometry.Fuchsian.circleArcEndpointNeighbor _ (E.symm x).val (E.symm (E (B
    (E.symm x)))).val
  rw [E.symm_apply_apply]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.circleFrontierArcMate_spec d.region_isOpen d.exterior d.exterior_not_closure d.unique_incidence _

/-- The actual original circle-region component traversed from a specified literal cut. -/
def component (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) : Set Circle :=
  (d.arcReversal_neighbor hw x).2.choose

theorem component_spec (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.component hw x ∈ ((fun z => connectedComponentIn
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius d.radius_pos) z) ''
        _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius d.radius_pos) ∧
      closure (d.component hw x) \ d.component hw x =
        {((d.cutEquiv hw).symm x).val,((d.cutEquiv hw).symm (d.arcReversal hw x)).val} :=
  (d.arcReversal_neighbor hw x).2.choose_spec

/-- Distinct actual alternating positions traverse genuinely disjoint compact
component arcs in the actual chart circle. -/
theorem alternating_component_closures_disjoint (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter
  P w)
    (m n : ℕ) (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
    (hne : (((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
      d.cuts_regular)*d.arcReversal hw)^m) x ≠
      (((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
        d.cuts_regular)*d.arcReversal hw)^n) x) :
    Disjoint
      (closure (d.component hw ((((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw
        d.radius d.cuts_regular)*d.arcReversal hw)^m) x)))
      (closure (d.component hw ((((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw
        d.radius d.cuts_regular)*d.arcReversal hw)^n) x))) :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.alternatingArc_component_closures_disjoint d.region_isOpen d.unique_incidence (d.cutEquiv hw)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
      d.cuts_regular) (d.arcReversal hw)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMate_involutive P w hw d.radius
      d.cuts_regular) (d.arcReversal_involutive hw)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMate_ne_self P w hw d.radius d.cuts_regular
      d.cuts_free) (d.arcReversal_ne_self hw)
    (d.component hw) (fun x => (d.component_spec hw x).1) (fun x => (d.component_spec hw x).2) m n x hne


/-- The genuine original-carrier coordinate on the actual chosen regular circle. -/
def coordinate (u : Circle) : P.domain.carrier :=
  (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w d.radius d.radius_pos u).val

theorem coordinate_continuous : Continuous d.coordinate :=
  continuous_subtype_val.comp (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w
    d.radius d.radius_pos).continuous

theorem coordinate_injective : Function.Injective d.coordinate :=
  Subtype.val_injective.comp (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w
    d.radius d.radius_pos).injective

theorem coordinate_cut_inverse (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.coordinate (((d.cutEquiv hw).symm x).val) = x.val := by
  have he (p : frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius
    d.radius_pos)) :
      ((d.cutEquiv hw) p).val = d.coordinate p.val := rfl
  simpa only [(d.cutEquiv hw).apply_symm_apply] using (he ((d.cutEquiv hw).symm x)).symm

/-- The actual open component arc in the original sphere-domain carrier. -/
def originalArc (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) : Set P.domain.carrier :=
  d.coordinate '' d.component hw x

theorem originalArc_subset_dirichlet (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.originalArc hw x ⊆ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w := by
  rintro y ⟨u,hu,rfl⟩
  have hs : d.component hw x ⊆ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius d.radius_pos := by
    obtain ⟨v,_hv,hvC⟩ := (d.component_spec hw x).1
    rw [←hvC]
    exact connectedComponentIn_subset _ _
  exact hs hu

theorem closure_originalArc_eq (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    closure (d.originalArc hw x) = d.coordinate '' closure (d.component hw x) :=
  d.coordinate_continuous.isClosedMap.closure_image_eq_of_continuous d.coordinate_continuous _

/-- The genuine compact original arc has exactly its two literal original cut endpoints. -/
theorem originalArc_endpoints (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    closure (d.originalArc hw x) \ d.originalArc hw x = {x.val,(d.arcReversal hw x).val} := by
  rw [d.closure_originalArc_eq]
  change d.coordinate '' closure (d.component hw x) \ d.coordinate '' d.component hw x = _
  rw [←image_sdiff d.coordinate_injective,(d.component_spec hw x).2,image_pair,
    d.coordinate_cut_inverse,d.coordinate_cut_inverse]

/-- Distinct alternating positions give disjoint actual compact arc closures
in the original carrier, not merely in a formal endpoint graph. -/
theorem alternating_original_closed_arcs_disjoint (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (m n : ℕ) (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
    (hne : (((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
      d.cuts_regular)*d.arcReversal hw)^m) x ≠
      (((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
        d.cuts_regular)*d.arcReversal hw)^n) x) :
    Disjoint
      (closure (d.originalArc hw ((((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw
        d.radius d.cuts_regular)*d.arcReversal hw)^m) x)))
      (closure (d.originalArc hw ((((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius d.cuts_regular)*d.arcReversal hw)^n) x))) := by
  rw [d.closure_originalArc_eq,d.closure_originalArc_eq]
  apply disjoint_left.mpr
  rintro p ⟨u,hu,heu⟩ ⟨v,hv,hev⟩
  have heuv : u = v := d.coordinate_injective (heu.trans hev.symm)
  exact disjoint_left.mp (d.alternating_component_closures_disjoint hw m n x hne) hu (heuv.symm ▸ hv)

end RegularDirichletCircleData
/-- Actual original polygon interiors cannot meet any group translate of an
actual original frontier point. -/
theorem fuchsian_polygon_interior_ne_translated_frontier
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    {v z : P.domain.carrier} (hv : v ∈ D) (hz : z ∈ frontier D) (g h : H) :
    g • v ≠ h • z := by
  intro he
  have hred : (h⁻¹*g) • v = z := by rw [mul_smul,he,inv_smul_smul]
  by_cases hunit : h⁻¹*g = 1
  · have hvz : v = z := by simpa only [hunit,one_smul] using hred
    exact hz.2 (hvz ▸ ((isFuchsianFundamentalDomain_iff P D).mp hD).1.interior_eq.symm ▸ hv)
  · exact disjoint_left.mp (hD.disjoint_image_closure hunit) ⟨v,hv,hred⟩ hz.1

/-- Distinct actual tiles separate arbitrary original interior subsets. -/
theorem fuchsian_polygon_translated_subsets_disjoint_of_tile_ne
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    {V W : Set P.domain.carrier} (hV : V ⊆ D) (hW : W ⊆ D)
    (g h : H) (hne : g ≠ h) : Disjoint (g • V) (h • W) := by
  apply disjoint_left.mpr
  rintro p ⟨v,hv,hgv⟩ ⟨z,hz,hgz⟩
  exact hne (fuchsian_polygon_interior_translate_unique hD (hV hv) (hW hz) g h (hgv.trans hgz.symm)).1

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- Distinct full developed states along the actual alternating orbit have
truly disjoint original-group-translated open arc interiors. -/
theorem alternating_translated_open_arcs_disjoint (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (m n : ℕ) (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (g h : H)
    (hne : (g,(((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
      d.cuts_regular)*d.arcReversal hw)^m) x) ≠
      (h,(((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
        d.cuts_regular)*d.arcReversal hw)^n) x)) :
    Disjoint
      (g • d.originalArc hw ((((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw
        d.radius d.cuts_regular)*d.arcReversal hw)^m) x))
      (h • d.originalArc hw ((((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius d.cuts_regular)*d.arcReversal hw)^n) x)) := by
  have hD := (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w
    hw).locallyFinite.fundamental
  by_cases hxy : (((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
    d.cuts_regular)*d.arcReversal hw)^m) x =
      (((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius
        d.cuts_regular)*d.arcReversal hw)^n) x
  · apply _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsian_polygon_translated_subsets_disjoint_of_tile_ne hD
      (d.originalArc_subset_dirichlet hw _) (d.originalArc_subset_dirichlet hw _) g h
    intro hgh
    exact hne (Prod.ext hgh hxy)
  · apply _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsian_polygon_translated_subsets_disjoint hD
      (d.originalArc_subset_dirichlet hw _) (d.originalArc_subset_dirichlet hw _) _ g h
    exact (d.alternating_original_closed_arcs_disjoint hw m n x hxy).mono subset_closure subset_closure


/-- Every specified actual original component has a genuine injective path with
exactly that compact closure as image and exactly that open arc after removing its
literal endpoints. Its entire actual path lies on the true global frontier. -/
theorem exists_arcPath (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    ∃ γ : Path x.val (d.arcReversal hw x).val, Function.Injective γ ∧
      range γ = closure (d.originalArc hw x) ∧
      range γ \ {x.val,(d.arcReversal hw x).val} = d.originalArc hw x ∧
      range γ ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  obtain ⟨δ,hδi,V,hV,hδrange,hδopen⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.circleArcEndpointNeighbor_path d.region_isOpen
    d.exterior d.exterior_not_closure (d.arcReversal_neighbor hw x)
  have hpV : ((d.cutEquiv hw).symm x).val ∈ closure V := by
    rw [←hδrange]
    exact ⟨0,δ.source⟩
  have hpC : ((d.cutEquiv hw).symm x).val ∈ closure (d.component hw x) := by
    have hh : ((d.cutEquiv hw).symm x).val ∈ closure (d.component hw x) \ d.component hw x := by
      rw [(d.component_spec hw x).2]
      exact mem_insert _ _
    exact hh.1
  have hVC : V = d.component hw x := _root_.LowDimensionalTopology.Geometry.Fuchsian.component_closure_intersection_eq_of_unique_incidence
    d.region_isOpen d.unique_incidence hV (d.component_spec hw x).1 hpV hpC
  let γ : Path x.val (d.arcReversal hw x).val := (δ.map d.coordinate_continuous).cast
    (d.coordinate_cut_inverse hw x).symm (d.coordinate_cut_inverse hw (d.arcReversal hw x)).symm
  have hγi : Function.Injective γ := d.coordinate_injective.comp hδi
  have hγrange : range γ = closure (d.originalArc hw x) := by
    change range (d.coordinate ∘ δ) = _
    rw [range_comp,hδrange,hVC]
    exact (d.closure_originalArc_eq hw x).symm
  have hpair : ({x.val,(d.arcReversal hw x).val} : Set P.domain.carrier) =
      d.coordinate '' {((d.cutEquiv hw).symm x).val,
        ((d.cutEquiv hw).symm (d.arcReversal hw x)).val} := by
    rw [image_pair,d.coordinate_cut_inverse,d.coordinate_cut_inverse]
  have hγopen : range γ \ {x.val,(d.arcReversal hw x).val} = d.originalArc hw x := by
    change range (d.coordinate ∘ δ) \ _ = d.coordinate '' d.component hw x
    rw [hpair,range_comp,←image_sdiff d.coordinate_injective,hδopen,hVC]
  refine ⟨γ,hγi,hγrange,hγopen,?_⟩
  intro y hy
  rw [hγrange,d.closure_originalArc_eq] at hy
  obtain ⟨u,hu,rfl⟩ := hy
  apply _root_.LowDimensionalTopology.Geometry.Fuchsian.closed_dirichlet_circle_subset_orbit_frontier P w d.radius d.radius_pos
  constructor
  · apply closure_mono (d.originalArc_subset_dirichlet hw x)
    rw [d.closure_originalArc_eq]
    exact ⟨u,hu,rfl⟩
  · exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w d.radius d.radius_pos
    u).property

/-- The selected genuine injective original component path. -/
def arcPath (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    Path x.val (d.arcReversal hw x).val := (d.exists_arcPath hw x).choose

theorem arcPath_spec (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    Function.Injective (d.arcPath hw x) ∧ range (d.arcPath hw x) = closure (d.originalArc hw x) ∧
      range (d.arcPath hw x) \ {x.val,(d.arcReversal hw x).val} = d.originalArc hw x ∧
      range (d.arcPath hw x) ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w
        d.radius) :=
  (d.exists_arcPath hw x).choose_spec

end RegularDirichletCircleData


/-- Joining two genuine injective paths whose full images meet only at their
common endpoint produces a genuine injective path without a constant initial pause. -/
theorem path_trans_injective_of_singleton_intersection
    {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hint : range γ ∩ range δ = {y}) : Function.Injective (γ.trans δ) := by
  have hcross (u v : I) (he : γ u = δ v) : u = 1 ∧ v = 0 := by
    have hm : γ u ∈ range γ ∩ range δ := ⟨mem_range_self u,he.symm ▸ mem_range_self v⟩
    have hval : γ u = y := by rwa [hint,mem_singleton_iff] at hm
    constructor
    · apply hγ
      exact hval.trans γ.target.symm
    · apply hδ
      exact he.symm.trans (hval.trans δ.source.symm)
  intro s t he
  simp only [Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · apply Subtype.ext
    have hh := congrArg Subtype.val (hγ he)
    change 2*(s:ℝ) = 2*(t:ℝ) at hh
    linarith
  · obtain ⟨hu,hv⟩ := hcross _ _ he
    have hu' := congrArg Subtype.val hu
    have hv' := congrArg Subtype.val hv
    change 2*(s:ℝ) = 1 at hu'
    change 2*(t:ℝ)-1 = 0 at hv'
    apply Subtype.ext
    linarith
  · obtain ⟨hu,hv⟩ := hcross _ _ he.symm
    have hu' := congrArg Subtype.val hu
    have hv' := congrArg Subtype.val hv
    change 2*(t:ℝ) = 1 at hu'
    change 2*(s:ℝ)-1 = 0 at hv'
    apply Subtype.ext
    linarith
  · apply Subtype.ext
    have hh := congrArg Subtype.val (hδ he)
    change 2*(s:ℝ)-1 = 2*(t:ℝ)-1 at hh
    linarith

/-- Positive-length actual development starts directly with the first original
arc. Every subsequent actual translated arc is appended without an initial constant path. -/
def equivariantPositiveArcDevelopment {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) : ∀ n, Path (x 0) (pathDevelopmentTransform t (n+1) • x (n+1))
  | 0 => (γ 0).cast rfl ((pathDevelopmentTransform_endpoint x b t ht 0).trans (one_smul _ _))
  | n + 1 => (equivariantPositiveArcDevelopment x b t ht γ n).trans
      (((γ (n+1)).map (continuous_const_smul (pathDevelopmentTransform t (n+1)))).cast rfl
        (pathDevelopmentTransform_endpoint x b t ht (n+1)))

/-- The positive development has exactly the same genuine geometric image as the
corresponding original development, while omitting its redundant initial pause. -/
theorem equivariantPositiveArcDevelopment_range {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (n : ℕ) :
    range (equivariantPositiveArcDevelopment x b t ht γ n) =
      range (equivariantPathDevelopment x b t ht γ (n+1)) := by
  induction n with
  | zero =>
      rw [equivariantPathDevelopment_range_succ]
      change range (γ 0) = range (Path.refl (x 0)) ∪ (1:G) • range (γ 0)
      rw [Path.refl_range,one_smul,singleton_union,insert_eq_of_mem]
      exact ⟨0,(γ 0).source⟩
  | succ n ih =>
      rw [equivariantPositiveArcDevelopment,Path.trans_range,equivariantPathDevelopment_range_succ,ih]
      congr 1
      change range ((fun u => pathDevelopmentTransform t (n+1) • u) ∘ γ (n+1)) = _
      rw [range_comp]
      rfl

/-- The positive development appends precisely the next genuine translated arc. -/
theorem equivariantPositiveArcDevelopment_range_succ {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (n : ℕ) :
    range (equivariantPositiveArcDevelopment x b t ht γ (n+1)) =
      range (equivariantPositiveArcDevelopment x b t ht γ n) ∪
        pathDevelopmentTransform t (n+1) • range (γ (n+1)) := by
  rw [equivariantPositiveArcDevelopment_range,equivariantPathDevelopment_range_succ,
    ←equivariantPositiveArcDevelopment_range]

/-- The exact genuine image of a positive development is its finite family of
actual translated compact arc images. -/
theorem equivariantPositiveArcDevelopment_range_finite_union {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (n : ℕ) :
    range (equivariantPositiveArcDevelopment x b t ht γ n) =
      ⋃ i ∈ Iic n, pathDevelopmentTransform t i • range (γ i) := by
  induction n with
  | zero =>
      change range (γ 0) = _
      ext p
      simp only [mem_iUnion,mem_Iic,Nat.le_zero]
      constructor
      · intro hp
        exact ⟨0,rfl,by simpa only [pathDevelopmentTransform,one_smul] using hp⟩
      · rintro ⟨i,rfl,hp⟩
        simpa only [pathDevelopmentTransform,one_smul] using hp
  | succ n ih =>
      rw [equivariantPositiveArcDevelopment_range_succ,ih]
      ext p
      simp only [mem_union,mem_iUnion,mem_Iic]
      constructor
      · rintro (⟨i,hi,hpi⟩ | hpi)
        · exact ⟨i,hi.trans (Nat.le_succ n),hpi⟩
        · exact ⟨n+1,le_rfl,hpi⟩
      · rintro ⟨i,hi,hpi⟩
        by_cases hin : i ≤ n
        · exact Or.inl ⟨i,hin,hpi⟩
        · have he : i = n+1 := by omega
          exact Or.inr (he ▸ hpi)

/-- Genuine injectivity of the constituent paths, exact single-endpoint incidence
of adjacent actual images and disjointness of nonadjacent actual images prove genuine
injectivity of every positive developed initial path. -/
theorem equivariantPositiveArcDevelopment_injective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (hγ : ∀ n, Function.Injective (γ n))
    (hjoin : ∀ n, (pathDevelopmentTransform t n • range (γ n)) ∩
      (pathDevelopmentTransform t (n+1) • range (γ (n+1))) =
        {pathDevelopmentTransform t (n+1) • x (n+1)})
    (hsep : ∀ i j, i+1 < j →
      Disjoint (pathDevelopmentTransform t i • range (γ i))
        (pathDevelopmentTransform t j • range (γ j))) (n : ℕ) :
    Function.Injective (equivariantPositiveArcDevelopment x b t ht γ n) := by
  induction n with
  | zero => exact hγ 0
  | succ n ih =>
      rw [equivariantPositiveArcDevelopment]
      apply path_trans_injective_of_singleton_intersection _ _ ih
      · exact (MulAction.injective (pathDevelopmentTransform t (n+1))).comp (hγ (n+1))
      · change range (equivariantPositiveArcDevelopment x b t ht γ n) ∩
          range ((fun u => pathDevelopmentTransform t (n+1) • u) ∘ γ (n+1)) = _
        rw [range_comp,equivariantPositiveArcDevelopment_range_finite_union]
        apply subset_antisymm
        · rintro p ⟨hp,hpj⟩
          obtain ⟨i,hpi⟩ := mem_iUnion.mp hp
          obtain ⟨hi,hpi⟩ := mem_iUnion.mp hpi
          by_cases he : i = n
          · subst i
            exact (Set.ext_iff.mp (hjoin n) p).mp ⟨hpi,hpj⟩
          · have hij : i+1 < n+1 := by
              have hin : i ≤ n := mem_Iic.mp hi
              omega
            exact False.elim (disjoint_left.mp (hsep i (n+1) hij) hpi hpj)
        · intro p hp
          have hp' : p ∈ (pathDevelopmentTransform t n • range (γ n)) ∩
              (pathDevelopmentTransform t (n+1) • range (γ (n+1))) :=
            (Set.ext_iff.mp (hjoin n) p).mpr hp
          exact ⟨mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨mem_Iic.mpr le_rfl,hp'.1⟩⟩,hp'.2⟩

/-- The same genuine injectivity criterion needs separation only for the finitely
many actual constituent arcs, so it applies before a first return in a closed cycle. -/
theorem equivariantPositiveArcDevelopment_injective_bounded {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (N : ℕ)
    (hγ : ∀ i ≤ N, Function.Injective (γ i))
    (hjoin : ∀ i < N, (pathDevelopmentTransform t i • range (γ i)) ∩
      (pathDevelopmentTransform t (i+1) • range (γ (i+1))) =
        {pathDevelopmentTransform t (i+1) • x (i+1)})
    (hsep : ∀ i j, j ≤ N → i+1 < j →
      Disjoint (pathDevelopmentTransform t i • range (γ i))
        (pathDevelopmentTransform t j • range (γ j))) :
    Function.Injective (equivariantPositiveArcDevelopment x b t ht γ N) := by
  have hall : ∀ m ≤ N, Function.Injective (equivariantPositiveArcDevelopment x b t ht γ m) := by
    intro m
    induction m with
    | zero => intro _hm; exact hγ 0 (Nat.zero_le N)
    | succ m ih =>
        intro hm
        have hmlt : m < N := (Nat.lt_succ_self m).trans_le hm
        rw [equivariantPositiveArcDevelopment]
        apply path_trans_injective_of_singleton_intersection _ _ (ih ((Nat.le_succ m).trans hm))
        · exact (MulAction.injective (pathDevelopmentTransform t (m+1))).comp (hγ (m+1) hm)
        · change range (equivariantPositiveArcDevelopment x b t ht γ m) ∩
            range ((fun u => pathDevelopmentTransform t (m+1) • u) ∘ γ (m+1)) = _
          rw [range_comp,equivariantPositiveArcDevelopment_range_finite_union]
          apply subset_antisymm
          · rintro p ⟨hp,hpj⟩
            obtain ⟨i,hpi⟩ := mem_iUnion.mp hp
            obtain ⟨hi,hpi⟩ := mem_iUnion.mp hpi
            by_cases he : i = m
            · subst i
              exact (Set.ext_iff.mp (hjoin m hmlt) p).mp ⟨hpi,hpj⟩
            · have hij : i+1 < m+1 := by
                have him : i ≤ m := mem_Iic.mp hi
                omega
              exact False.elim (disjoint_left.mp (hsep i (m+1) hm hij) hpi hpj)
          · intro p hp
            have hp' : p ∈ (pathDevelopmentTransform t m • range (γ m)) ∩
                (pathDevelopmentTransform t (m+1) • range (γ (m+1))) :=
              (Set.ext_iff.mp (hjoin m hmlt) p).mpr hp
            exact ⟨mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨mem_Iic.mpr le_rfl,hp'.1⟩⟩,hp'.2⟩
  exact hall N le_rfl



/-- For genuine compact arc images with disjoint open interiors and no endpoint
inside the other open arc, every actual intersection lies in both literal endpoint pairs. -/
theorem compact_arcs_inter_subset_endpoints {X : Type*}
    {C D O V : Set X} {x y u v : X}
    (hC : C \ O = {x,y}) (hD : D \ V = {u,v})
    (hOV : Disjoint O V) (hxy : x ∉ V ∧ y ∉ V) (huv : u ∉ O ∧ v ∉ O) :
    C ∩ D ⊆ ({x,y} : Set X) ∩ {u,v} := by
  rintro p ⟨hpC,hpD⟩
  have hpO : p ∉ O := by
    intro hh
    have hpV : p ∉ V := fun h => disjoint_left.mp hOV hh h
    have hpUV : p ∈ ({u,v} : Set X) := by rw [←hD]; exact ⟨hpD,hpV⟩
    rcases mem_insert_iff.mp hpUV with he | he
    · exact huv.1 (he ▸ hh)
    · exact huv.2 (mem_singleton_iff.mp he ▸ hh)
  have hpV : p ∉ V := by
    intro hh
    have hpXY : p ∈ ({x,y} : Set X) := by rw [←hC]; exact ⟨hpC,hpO⟩
    rcases mem_insert_iff.mp hpXY with he | he
    · exact hxy.1 (he ▸ hh)
    · exact hxy.2 (mem_singleton_iff.mp he ▸ hh)
  constructor
  · rw [←hC]
    exact ⟨hpC,hpO⟩
  · rw [←hD]
    exact ⟨hpD,hpV⟩

/-- Distinct literal endpoint pairs and the genuine open-arc separation data
force the full actual compact arcs to be disjoint. -/
theorem compact_arcs_disjoint_of_endpoint_pairs_disjoint {X : Type*}
    {C D O V : Set X} {x y u v : X}
    (hC : C \ O = {x,y}) (hD : D \ V = {u,v})
    (hOV : Disjoint O V) (hxy : x ∉ V ∧ y ∉ V) (huv : u ∉ O ∧ v ∉ O)
    (hEnds : Disjoint ({x,y} : Set X) {u,v}) : Disjoint C D := by
  apply disjoint_left.mpr
  intro p hpC hpD
  have hh := compact_arcs_inter_subset_endpoints hC hD hOV hxy huv ⟨hpC,hpD⟩
  exact disjoint_left.mp hEnds hh.1 hh.2

/-- Genuine adjacent compact arcs with no other common endpoint meet exactly
at their literal shared endpoint. -/
theorem compact_arcs_inter_eq_shared_endpoint {X : Type*}
    {C D O V : Set X} {x y z : X}
    (hC : C \ O = {x,y}) (hD : D \ V = {y,z})
    (hOV : Disjoint O V) (hxy : x ∉ V ∧ y ∉ V) (hyz : y ∉ O ∧ z ∉ O)
    (hxyNe : x ≠ y) (hxzNe : x ≠ z) : C ∩ D = {y} := by
  apply subset_antisymm
  · intro p hp
    have hh := compact_arcs_inter_subset_endpoints hC hD hOV hxy hyz hp
    rcases mem_insert_iff.mp hh.1 with hpX | hpY
    · rcases mem_insert_iff.mp hh.2 with hpY | hpZ
      · exact False.elim (hxyNe (hpX.symm.trans hpY))
      · exact False.elim (hxzNe (hpX.symm.trans (mem_singleton_iff.mp hpZ)))
    · exact hpY
  · intro p hp
    have hpY : p = y := mem_singleton_iff.mp hp
    subst p
    have hCy : y ∈ C \ O := by rw [hC]; exact mem_insert_of_mem _ (mem_singleton _)
    have hDy : y ∈ D \ V := by rw [hD]; exact mem_insert _ _
    exact ⟨hCy.1,hDy.1⟩

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The actual original group pairing on the literal regular cut set. -/
def pairing (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P
  w) : Equiv.Perm (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCutPairing P w hw d.radius d.cuts_regular

/-- The actual invertible step records both original cut and accumulated original tile. -/
def endpointStep (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) : Equiv.Perm (H ×
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.endpointSkewPermutation (d.pairing hw*d.arcReversal hw)
    (fun z => (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMateElement P w hw d.radius d.cuts_regular
      (d.arcReversal hw z))⁻¹)

def state (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    H × _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius := ((d.endpointStep
      hw)^n) (1,x)

/-- The genuine original-carrier vertex of a developed state. -/
def vertex (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    P.domain.carrier := (d.state hw x n).1 • (d.state hw x n).2.val

/-- The actual translated open original arc at a developed state. -/
def developedOpenArc (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    Set P.domain.carrier := (d.state hw x n).1 • d.originalArc hw (d.state hw x n).2

/-- The actual translated genuine compact arc at a developed state. -/
def developedClosedArc (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    Set P.domain.carrier := (d.state hw x n).1 • closure (d.originalArc hw (d.state hw x n).2)

theorem state_snd (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    (d.state hw x n).2 = ((d.pairing hw*d.arcReversal hw)^n) x :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.endpointSkewPermutation_pow_snd _ _ n 1 x

theorem state_succ (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    d.state hw x (n+1) =
      ((d.state hw x n).1 * (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMateElement P w hw d.radius
        d.cuts_regular
        (d.arcReversal hw (d.state hw x n).2))⁻¹,
        d.pairing hw (d.arcReversal hw (d.state hw x n).2)) := by
  dsimp only [state]
  rw [pow_succ',Equiv.Perm.mul_apply]
  rfl

/-- The actual terminal endpoint of one developed arc is the actual starting vertex of the next. -/
theorem vertex_next (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    d.vertex hw x (n+1) = (d.state hw x n).1 • (d.arcReversal hw (d.state hw x n).2).val := by
  rw [vertex,d.state_succ]
  change ((d.state hw x n).1 * (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMateElement P w hw
    d.radius d.cuts_regular
    (d.arcReversal hw (d.state hw x n).2))⁻¹) •
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMateElement P w hw d.radius d.cuts_regular
        (d.arcReversal hw (d.state hw x n).2) • (d.arcReversal hw (d.state hw x n).2).val) = _
  rw [mul_smul,inv_smul_smul]

/-- Coincidence of genuine developed vertices is exactly repetition of the full
actual tile-and-cut state. -/
theorem vertex_eq_iff_state_eq (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (m n : ℕ) :
    d.vertex hw x m = d.vertex hw x n ↔ d.state hw x m = d.state hw x n :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichlet_endpointSkewPermutation_start_eq_iff P w hw d.radius d.cuts_regular
    (d.pairing hw) (d.arcReversal hw)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMate_involutive P w hw d.radius
      d.cuts_regular) (d.arcReversal_involutive hw)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMate_ne_self P w hw d.radius d.cuts_regular
      d.cuts_free) (d.arcReversal_ne_self hw)
    rfl (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleMateElement P w hw d.radius
      d.cuts_regular) m n x

/-- The genuine compact developed arc has precisely its actual successive vertices as endpoints. -/
theorem developedClosedArc_endpoints (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    d.developedClosedArc hw x n \ d.developedOpenArc hw x n =
      {d.vertex hw x n,d.vertex hw x (n+1)} := by
  change ((fun z => (d.state hw x n).1 • z) '' closure (d.originalArc hw (d.state hw x n).2)) \
    ((fun z => (d.state hw x n).1 • z) '' d.originalArc hw (d.state hw x n).2) = _
  rw [←image_sdiff (MulAction.injective (d.state hw x n).1),d.originalArc_endpoints,image_pair,d.vertex_next]
  rfl

/-- Distinct full actual developed states have genuinely disjoint open arc interiors. -/
theorem developedOpenArc_disjoint_of_state_ne (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P
  w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (m n : ℕ)
    (hne : d.state hw x m ≠ d.state hw x n) :
    Disjoint (d.developedOpenArc hw x m) (d.developedOpenArc hw x n) := by
  change ((d.state hw x m).1,(d.state hw x m).2) ≠
    ((d.state hw x n).1,(d.state hw x n).2) at hne
  rw [d.state_snd,d.state_snd] at hne
  change Disjoint ((d.state hw x m).1 • d.originalArc hw (d.state hw x m).2)
    ((d.state hw x n).1 • d.originalArc hw (d.state hw x n).2)
  rw [d.state_snd,d.state_snd]
  exact d.alternating_translated_open_arcs_disjoint hw m n x _ _ hne

/-- No actual developed vertex lies in any of the actual developed open arc interiors. -/
theorem vertex_not_mem_developedOpenArc (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (m n : ℕ) :
    d.vertex hw x n ∉ d.developedOpenArc hw x m := by
  rintro ⟨v,hv,he⟩
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsian_polygon_interior_ne_translated_frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w hw).locallyFinite.fundamental
    (d.originalArc_subset_dirichlet hw _ hv) (d.state hw x n).2.property.1
    (d.state hw x m).1 (d.state hw x n).1 he


/-- Before an actual developed-state return, adjacent genuine compact original
arcs intersect at precisely their shared actual original vertex. -/
theorem developedClosedArc_adjacent_intersection (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter
  P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ)
    (h01 : d.state hw x n ≠ d.state hw x (n+1))
    (h02 : d.state hw x n ≠ d.state hw x (n+2)) :
    d.developedClosedArc hw x n ∩ d.developedClosedArc hw x (n+1) =
      {d.vertex hw x (n+1)} := by
  apply _root_.LowDimensionalTopology.Geometry.Fuchsian.compact_arcs_inter_eq_shared_endpoint (d.developedClosedArc_endpoints hw x n)
    (d.developedClosedArc_endpoints hw x (n+1)) (d.developedOpenArc_disjoint_of_state_ne hw x n (n+1) h01)
  · exact ⟨d.vertex_not_mem_developedOpenArc hw x (n+1) n,
      d.vertex_not_mem_developedOpenArc hw x (n+1) (n+1)⟩
  · exact ⟨d.vertex_not_mem_developedOpenArc hw x n (n+1),
      d.vertex_not_mem_developedOpenArc hw x n (n+2)⟩
  · exact fun he => h01 ((d.vertex_eq_iff_state_eq hw x n (n+1)).mp he)
  · exact fun he => h02 ((d.vertex_eq_iff_state_eq hw x n (n+2)).mp he)

/-- Four distinct actual endpoint states separate the full genuine nonadjacent
compact original arcs, including their literal endpoints. -/
theorem developedClosedArc_disjoint_of_endpoint_states (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (m n : ℕ)
    (h00 : d.state hw x m ≠ d.state hw x n)
    (h01 : d.state hw x m ≠ d.state hw x (n+1))
    (h10 : d.state hw x (m+1) ≠ d.state hw x n)
    (h11 : d.state hw x (m+1) ≠ d.state hw x (n+1)) :
    Disjoint (d.developedClosedArc hw x m) (d.developedClosedArc hw x n) := by
  apply _root_.LowDimensionalTopology.Geometry.Fuchsian.compact_arcs_disjoint_of_endpoint_pairs_disjoint (d.developedClosedArc_endpoints hw x m)
    (d.developedClosedArc_endpoints hw x n) (d.developedOpenArc_disjoint_of_state_ne hw x m n h00)
  · exact ⟨d.vertex_not_mem_developedOpenArc hw x n m,
      d.vertex_not_mem_developedOpenArc hw x n (m+1)⟩
  · exact ⟨d.vertex_not_mem_developedOpenArc hw x m n,
      d.vertex_not_mem_developedOpenArc hw x m (n+1)⟩
  · apply disjoint_left.mpr
    intro p hpM hpN
    rcases mem_insert_iff.mp hpM with hpM | hpM
    · rcases mem_insert_iff.mp hpN with hpN | hpN
      · exact h00 ((d.vertex_eq_iff_state_eq hw x m n).mp (hpM.symm.trans hpN))
      · exact h01 ((d.vertex_eq_iff_state_eq hw x m (n+1)).mp (hpM.symm.trans (mem_singleton_iff.mp hpN)))
    · rcases mem_insert_iff.mp hpN with hpN | hpN
      · exact h10 ((d.vertex_eq_iff_state_eq hw x (m+1) n).mp ((mem_singleton_iff.mp hpM).symm.trans hpN))
      · exact h11 ((d.vertex_eq_iff_state_eq hw x (m+1) (n+1)).mp
          ((mem_singleton_iff.mp hpM).symm.trans (mem_singleton_iff.mp hpN)))

/-- The actual translated injective component path with its consecutive actual
original vertices, without a constant initial segment. -/
def developedPath (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    Path (d.vertex hw x n) (d.vertex hw x (n+1)) :=
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  ((d.arcPath hw (d.state hw x n).2).map (continuous_const_smul (d.state hw x n).1)).cast rfl
    (d.vertex_next hw x n)

/-- This genuine injective original path has exactly the actual developed compact arc as image. -/
theorem developedPath_spec (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    Function.Injective (d.developedPath hw x n) ∧
      range (d.developedPath hw x n) = d.developedClosedArc hw x n := by
  constructor
  · exact (MulAction.injective (d.state hw x n).1).comp (d.arcPath_spec hw (d.state hw x n).2).1
  · change range ((fun z => (d.state hw x n).1 • z) ∘ d.arcPath hw (d.state hw x n).2) = _
    rw [range_comp,(d.arcPath_spec hw (d.state hw x n).2).2.1]
    rfl


/-- Every genuine developed compact arc lies on the literal original full-orbit frontier. -/
theorem developedClosedArc_subset_frontier (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (n : ℕ) :
    d.developedClosedArc hw x n ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  rintro y ⟨z,hz,he⟩
  have hzF : z ∈ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
    apply (d.arcPath_spec hw (d.state hw x n).2).2.2.2
    rw [(d.arcPath_spec hw (d.state hw x n).2).2.1]
    exact hz
  have hy : (d.state hw x n).1 • z ∈
      (d.state hw x n).1 • frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w
        d.radius) := smul_mem_smul_set hzF
  change (d.state hw x n).1 • z = y at he
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion_frontier_invariant,he] at hy
  exact hy

/-- Before the first actual full-state return, the finite developed original arc
chain has a genuine injective parametrization with its exact actual compact image.
The separation assumptions here concern the already constructed original tile-and-cut
states; no presumed geometric injectivity or simple-curve property is assumed. -/
theorem exists_injective_developed_path_before_return (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (N : ℕ)
    (hStates : Set.InjOn (d.state hw x) (Iic (N+1))) :
    ∃ Γ : Path x.val (d.vertex hw x (N+1)), Function.Injective Γ ∧
      range Γ = ⋃ i ∈ Iic N, d.developedClosedArc hw x i ∧
      range Γ ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  let v := d.vertex hw x
  let ψ := d.developedPath hw x
  let t : ℕ → H := fun _ => 1
  have ht (n : ℕ) : t n • v (n+1) = v (n+1) := one_smul _ _
  have hT (n : ℕ) : _root_.LowDimensionalTopology.Geometry.Fuchsian.pathDevelopmentTransform t n = 1 := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.pathDevelopmentTransform,ih,t,inv_one,mul_one]
  have hne (i j : ℕ) (hi : i ≤ N+1) (hj : j ≤ N+1) (hij : i ≠ j) :
      d.state hw x i ≠ d.state hw x j :=
    fun he => hij (hStates (mem_Iic.mpr hi) (mem_Iic.mpr hj) he)
  have hjoin (i : ℕ) (hi : i < N) : range (ψ i) ∩ range (ψ (i+1)) = {v (i+1)} := by
    change range (d.developedPath hw x i) ∩ range (d.developedPath hw x (i+1)) = _
    rw [(d.developedPath_spec hw x i).2,(d.developedPath_spec hw x (i+1)).2]
    apply d.developedClosedArc_adjacent_intersection hw x i
    · apply hne <;> omega
    · apply hne <;> omega
  have hsep (i j : ℕ) (hj : j ≤ N) (hij : i+1 < j) : Disjoint (range (ψ i)) (range (ψ j)) := by
    change Disjoint (range (d.developedPath hw x i)) (range (d.developedPath hw x j))
    rw [(d.developedPath_spec hw x i).2,(d.developedPath_spec hw x j).2]
    apply d.developedClosedArc_disjoint_of_endpoint_states hw x i j <;> apply hne <;> omega
  let Γ₀ := _root_.LowDimensionalTopology.Geometry.Fuchsian.equivariantPositiveArcDevelopment v (fun n => v
    (n+1)) t ht ψ N
  have hΓi : Function.Injective Γ₀ := by
    apply _root_.LowDimensionalTopology.Geometry.Fuchsian.equivariantPositiveArcDevelopment_injective_bounded v (fun n
      => v (n+1)) t ht ψ N
    · intro i _hi
      exact (d.developedPath_spec hw x i).1
    · intro i hi
      simpa only [hT,one_smul] using hjoin i hi
    · intro i j hj hij
      simpa only [hT,one_smul] using hsep i j hj hij
  have hΓrange : range Γ₀ = ⋃ i ∈ Iic N, d.developedClosedArc hw x i := by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.equivariantPositiveArcDevelopment_range_finite_union]
    simp only [hT,one_smul]
    apply iUnion_congr
    intro i
    apply iUnion_congr
    intro _hi
    exact (d.developedPath_spec hw x i).2
  have hvzero : v 0 = x.val := by
    simp only [v,vertex,state,pow_zero,Equiv.Perm.one_apply,one_smul]
  have htarget : d.vertex hw x (N+1) = _root_.LowDimensionalTopology.Geometry.Fuchsian.pathDevelopmentTransform t (N+1) • v (N+1) := by
    rw [hT,one_smul]
  let Γ : Path x.val (d.vertex hw x (N+1)) := Γ₀.cast hvzero.symm htarget
  refine ⟨Γ,hΓi,hΓrange,?_⟩
  intro p hp
  change p ∈ range Γ₀ at hp
  rw [hΓrange] at hp
  obtain ⟨i,hpi⟩ := mem_iUnion.mp hp
  obtain ⟨_hi,hpi⟩ := mem_iUnion.mp hpi
  exact d.developedClosedArc_subset_frontier hw x i hpi

end RegularDirichletCircleData
/-- An invertible genuine state motion with no positive return has a genuinely
injective nonnegative orbit, with no finite-state model substituted for its orbit. -/
theorem perm_power_orbit_injective_of_no_return {X : Type*} (F : Equiv.Perm X) (x : X)
    (hno : ∀ n : ℕ, 0 < n → (F^n) x ≠ x) : Function.Injective (fun n : ℕ => (F^n) x) := by
  have hle (m n : ℕ) (hmn : m ≤ n) (he : (F^m) x = (F^n) x) : m = n := by
    by_contra hne
    have hlt : m < n := by omega
    have hret : (F^(n-m)) x = x := by
      apply (F^m).injective
      calc
        (F^m) ((F^(n-m)) x) = (F^n) x := by
          rw [←Equiv.Perm.mul_apply,←pow_add,Nat.add_sub_of_le hmn]
        _ = (F^m) x := he.symm
    exact hno (n-m) (Nat.sub_pos_of_lt hlt) hret
  intro m n he
  rcases le_total m n with hmn | hnm
  · exact hle m n hmn he
  · exact (hle n m hnm he.symm).symm

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The true first positive return period of the full actual tile-and-cut state;
zero means that this genuine invertible orbit is not periodic. -/
def endpointPeriod (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) : ℕ :=
  Function.minimalPeriod (d.endpointStep hw) (1,x)

theorem state_injOn_before_period (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    Set.InjOn (d.state hw x) (Iio (d.endpointPeriod hw x)) := by
  intro m hm n hn he
  apply Function.iterate_injOn_Iio_minimalPeriod hm hn
  simpa only [state,Equiv.Perm.coe_pow] using he

/-- The original developed path is genuinely injective throughout every finite
prefix preceding the actual first full-state return, with no separate geometric
injectivity hypothesis. -/
theorem exists_injective_developed_path_lt_period (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (N : ℕ) (hN : N+1 <
      d.endpointPeriod hw x) :
    ∃ Γ : Path x.val (d.vertex hw x (N+1)), Function.Injective Γ ∧
      range Γ = ⋃ i ∈ Iic N, d.developedClosedArc hw x i ∧
      range Γ ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  apply d.exists_injective_developed_path_before_return hw x N
  intro i hi j hj he
  exact d.state_injOn_before_period hw x ((mem_Iic.mp hi).trans_lt hN) ((mem_Iic.mp hj).trans_lt hN) he

/-- In the genuine nonperiodic case the entire actual nonnegative developed-state
orbit is injective. -/
theorem state_injective_of_period_zero (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0) :
    Function.Injective (d.state hw x) := by
  apply _root_.LowDimensionalTopology.Geometry.Fuchsian.perm_power_orbit_injective_of_no_return (d.endpointStep
    hw) (1,x)
  intro n hn he
  have hret : Function.IsPeriodicPt (d.endpointStep hw) n (1,x) := by
    change ((d.endpointStep hw : (H × _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
      → _)^[n]) (1,x) = (1,x)
    simpa only [Equiv.Perm.coe_pow] using he
  have hp : 0 < d.endpointPeriod hw x := hret.minimalPeriod_pos hn
  rw [hzero] at hp
  exact (Nat.lt_irrefl 0) hp

/-- In the actual nonperiodic case every finite genuine developed prefix has an
injective original-carrier parametrization and its exact geometric compact image. -/
theorem exists_injective_developed_path_of_period_zero (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0) (N : ℕ) :
    ∃ Γ : Path x.val (d.vertex hw x (N+1)), Function.Injective Γ ∧
      range Γ = ⋃ i ∈ Iic N, d.developedClosedArc hw x i ∧
      range Γ ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) :=
  d.exists_injective_developed_path_before_return hw x N (d.state_injective_of_period_zero hw x hzero).injOn

end RegularDirichletCircleData
end LowDimensionalTopology.Geometry.Fuchsian
