module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.PolygonCompactCircleCores
public import Mathlib.Topology.Connected.LocallyConnected
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletCirclePairing
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineDistance
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Pointwise UpperHalfPlane RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance orbitBallSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance orbitBallSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The literal original closed-polygon core cut out by a genuine open hyperbolic ball. -/
def fuchsianOpenPolygonCore {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (w : P.domain.carrier) (R : ℝ) : Set P.domain.carrier :=
  closure D ∩ {x | P.hyperbolicDist w x < R}

/-- The genuine union of equal-radius hyperbolic balls about the full actual group orbit. -/
def fuchsianOrbitBallUnion {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) : Set P.domain.carrier :=
  ⋃ g : H, {x | P.hyperbolicDist (g • w) x < R}

theorem fuchsianOrbitBallUnion_isOpen {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) :
    IsOpen (fuchsianOrbitBallUnion P w R) := by
  apply isOpen_iUnion
  intro g
  change IsOpen {x | dist (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate x) < R}
  exact isOpen_lt (continuous_const.dist P.halfPlaneCoordinate.continuous) continuous_const

theorem fuchsianOrbitBallUnion_invariant {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (g : H) :
    g • fuchsianOrbitBallUnion P w R = fuchsianOrbitBallUnion P w R := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨h,hh⟩ := mem_iUnion.mp hu
    change P.hyperbolicDist (h • w) u < R at hh
    apply mem_iUnion.mpr
    refine ⟨g*h,?_⟩
    change P.hyperbolicDist ((g*h) • w) (g • u) < R
    simpa only [mul_smul,P.hyperbolicDist_smul] using hh
  · intro hx
    obtain ⟨h,hh⟩ := mem_iUnion.mp hx
    change P.hyperbolicDist (h • w) x < R at hh
    refine ⟨g⁻¹ • x,mem_iUnion.mpr ⟨g⁻¹*h,?_⟩,smul_inv_smul g x⟩
    change P.hyperbolicDist ((g⁻¹*h) • w) (g⁻¹ • x) < R
    simpa only [mul_smul,P.hyperbolicDist_smul] using hh

/-- In the actual closed Dirichlet polygon, the full orbit-ball condition is exactly the genuine center-ball condition. -/
theorem dirichlet_closed_mem_orbitBallUnion_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ)
    {x : P.domain.carrier} (hx : x ∈ closure (dirichletDomain P w)) :
    x ∈ fuchsianOrbitBallUnion P w R ↔ P.hyperbolicDist w x < R := by
  constructor
  · intro hxu
    obtain ⟨g,hg⟩ := mem_iUnion.mp hxu
    change P.hyperbolicDist (g • w) x < R at hg
    have he := closure_dirichletDomain_le P w hx g
    rw [P.hyperbolicDist_comm x w] at he
    exact he.trans_lt (by simpa only [P.hyperbolicDist_comm] using hg)
  · intro hxR
    exact mem_iUnion.mpr ⟨1,by change P.hyperbolicDist ((1 : H) • w) x < R; simpa only [one_smul] using hxR⟩

/-- Saturating the genuine open-ball Dirichlet core gives exactly the full true orbit-ball union. -/
theorem dirichlet_open_core_saturation_eq_orbitBallUnion {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ) :
    (⋃ g : H, g • fuchsianOpenPolygonCore P (dirichletDomain P w) w R) =
      fuchsianOrbitBallUnion P w R := by
  ext x
  constructor
  · intro hx
    obtain ⟨g,u,hu,rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨g,by
      change P.hyperbolicDist (g • w) (g • u) < R
      have huR : P.hyperbolicDist w u < R := hu.2
      simpa only [P.hyperbolicDist_smul] using huR⟩
  · intro hx
    have hcov : x ∈ ⋃ g : H, (fun u : P.domain.carrier => g • u) '' closure (dirichletDomain P w) := by
      rw [(dirichletDomain_fundamental P w hw).closure_cover]
      trivial
    obtain ⟨g,u,hu,hgu⟩ := mem_iUnion.mp hcov
    change g • u = x at hgu
    have hback : g⁻¹ • x ∈ g⁻¹ • fuchsianOrbitBallUnion P w R := ⟨x,hx,rfl⟩
    rw [fuchsianOrbitBallUnion_invariant,←hgu,inv_smul_smul] at hback
    have huR := (dirichlet_closed_mem_orbitBallUnion_iff P w R hu).mp hback
    exact mem_iUnion.mpr ⟨g,u,⟨hu,huR⟩,hgu⟩

/-- A genuine positive open-ball core in an actual closed convex polygon is connected. -/
theorem fuchsian_open_polygon_core_connected
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (hw : w ∈ D)
    (R : ℝ) (hR : 0 < R) : IsConnected (fuchsianOpenPolygonCore P D w R) := by
  let φ := P.halfPlaneCoordinate
  let A : Set ℍ := (φ '' closure D) ∩ Metric.ball (φ w) R
  have he : fuchsianOpenPolygonCore P D w R = φ.symm '' A := by
    ext z
    constructor
    · rintro ⟨hz,hzR⟩
      change dist (φ w) (φ z) < R at hzR
      exact ⟨φ z,⟨⟨z,hz,rfl⟩,by simpa only [Metric.mem_ball,dist_comm] using hzR⟩,φ.symm_apply_apply z⟩
    · rintro ⟨u,⟨⟨z,hz,hzu⟩,huR⟩,rfl⟩
      rw [←hzu,φ.symm_apply_apply]
      refine ⟨hz,?_⟩
      change dist (φ w) (φ z) < R
      simpa only [Metric.mem_ball,hzu,dist_comm] using huR
  have hcD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (φ '' D) := by
    have hh := hD.normalized_hConvex (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    rw [map_one] at hh
    simpa using hh
  have hcCl : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (φ '' closure D) := by rw [φ.image_closure]; exact hcD.closure
  have hcA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex A := fun z hz u hu v hv =>
    ⟨hcCl z hz.1 u hu.1 hv,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_metric_ball (φ w) R) z hz.2 u hu.2
      hv⟩
  rw [he]
  refine ⟨?_,hcA.isPreconnected.image φ.symm φ.symm.continuous.continuousOn⟩
  exact ⟨w,φ w,⟨⟨w,subset_closure hw,rfl⟩,by simpa only [Metric.mem_ball,dist_self] using hR⟩,
    φ.symm_apply_apply w⟩

/-- Actual finite generation makes every sufficiently large full orbit-ball neighborhood genuinely connected and open. -/
theorem finitelyGenerated_cofinal_orbitBallUnions_connected
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (hFG :
      H.FG)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ < R →
      IsOpen (fuchsianOrbitBallUnion P w R) ∧ IsConnected (fuchsianOrbitBallUnion P w R) := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  have hwD := dirichletDomain_center_mem P w hw
  obtain ⟨R₀,hR₀,T,_hTf,_hTS,hTgen,hcore⟩ :=
    finitelyGenerated_cofinal_polygon_ball_cores hD hFG w hwD
  refine ⟨R₀,hR₀,?_⟩
  intro R hR
  have hsub : fuchsianClosedPolygonCore P (dirichletDomain P w) w R₀ ⊆
      fuchsianOpenPolygonCore P (dirichletDomain P w) w R :=
    fun _ hx => ⟨hx.1,hx.2.trans_lt hR⟩
  have hc := fuchsian_open_polygon_core_connected hD w hwD R (hR₀.trans hR)
  have hover (g : H) (hg : g ∈ T) :
      (fuchsianOpenPolygonCore P (dirichletDomain P w) w R ∩
        g • fuchsianOpenPolygonCore P (dirichletDomain P w) w R).Nonempty :=
    ((hcore R₀ le_rfl).2.2.2 g hg).mono (inter_subset_inter hsub (image_mono hsub))
  refine ⟨fuchsianOrbitBallUnion_isOpen P w R,?_⟩
  rw [←dirichlet_open_core_saturation_eq_orbitBallUnion P w hw R]
  exact connected_orbit_union_of_generators _ hc T hTgen hover



/-- A genuine bounded nonempty connected open real set is precisely its open endpoint interval. -/
theorem real_bounded_connected_open_eq_Ioo {S : Set ℝ} (hc : IsConnected S) (ho : IsOpen S)
    (hbelow : BddBelow S) (habove : BddAbove S) : S = Ioo (sInf S) (sSup S) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp ho x hx
    have hleft : x-r/2 ∈ S := hball (by rw [Metric.mem_ball,Real.dist_eq]; rw [sub_sub_cancel_left,abs_neg,abs_of_pos (half_pos hr)]; exact half_lt_self hr)
    have hright : x+r/2 ∈ S := hball (by rw [Metric.mem_ball,Real.dist_eq]; rw [add_sub_cancel_left,abs_of_pos (half_pos hr)]; exact half_lt_self hr)
    exact ⟨(csInf_le hbelow hleft).trans_lt (by linarith),
      (show x < x+r/2 by linarith).trans_le (le_csSup habove hright)⟩
  · exact hc.Ioo_csInf_csSup_subset hbelow habove

/-- A genuine circle point different from the chosen argument cut has argument strictly below pi. -/
theorem circle_arg_lt_pi_of_ne_exp_pi {u : Circle} (hu : u ≠ Circle.exp Real.pi) :
    Complex.arg (u : ℂ) < Real.pi := by
  apply lt_of_le_of_ne (Complex.arg_le_pi _)
  intro he
  apply hu
  rw [←he]
  exact (Circle.exp_arg u).symm

/-- The actual circle with one point removed is genuinely homeomorphic to the open angle interval. -/
def circleSlitAngleHomeomorph :
    {u : Circle | u ≠ Circle.exp Real.pi} ≃ₜ Ioo (-Real.pi) Real.pi where
  toFun u := ⟨Complex.arg (u.val : ℂ),Complex.neg_pi_lt_arg _,circle_arg_lt_pi_of_ne_exp_pi u.property⟩
  invFun t := ⟨Circle.exp t.val,by
    intro he
    have hh := Circle.exp_injOn_Ioc (show Real.pi-(-Real.pi) ≤ 2*Real.pi by ring_nf; exact le_rfl)
      (show t.val ∈ Ioc (-Real.pi) Real.pi from ⟨t.property.1,t.property.2.le⟩)
      (show Real.pi ∈ Ioc (-Real.pi) Real.pi from ⟨by linarith [Real.pi_pos],le_rfl⟩) he
    exact t.property.2.ne hh⟩
  left_inv u := Subtype.ext (Circle.exp_arg u.val)
  right_inv t := Subtype.ext (Circle.arg_exp t.property.1 t.property.2.le)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro u
    have hs : (u.val : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff_arg.mpr
      ⟨(circle_arg_lt_pi_of_ne_exp_pi u.property).ne,u.val.coe_ne_zero⟩
    have hc : Continuous (fun v : {u : Circle | u ≠ Circle.exp Real.pi} => (v.val : ℂ)) :=
      continuous_subtype_val.comp continuous_subtype_val
    change ContinuousAt (fun v : {u : Circle | u ≠ Circle.exp Real.pi} => Complex.arg (v.val : ℂ)) u
    exact ContinuousAt.comp (f := fun v : {u : Circle | u ≠ Circle.exp Real.pi} => (v.val : ℂ))
      (x := u) (Complex.continuousAt_arg hs) hc.continuousAt
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Circle.exp.continuous.comp continuous_subtype_val

/-- Removing any specified actual circle point gives the same genuine open-interval chart. -/
def circlePuncturedAngleHomeomorph (a : Circle) :
    {u : Circle | u ≠ a} ≃ₜ Ioo (-Real.pi) Real.pi := by
  let e : Circle ≃ₜ Circle := Homeomorph.mulLeft (Circle.exp Real.pi*a⁻¹)
  have hea : e a = Circle.exp Real.pi := by change Circle.exp Real.pi*a⁻¹*a = _; simp [mul_assoc]
  have hiff (u : Circle) : u ≠ a ↔ e u ≠ Circle.exp Real.pi := by
    rw [←hea,e.injective.ne_iff]
  exact (e.subtype hiff).trans circleSlitAngleHomeomorph


/-- The complete actual circle parametrization extending the punctured angle chart. -/
def circleArcParam (a : Circle) (t : ℝ) : Circle := a / Circle.exp Real.pi * Circle.exp t

theorem continuous_circleArcParam (a : Circle) : Continuous (circleArcParam a) :=
  continuous_const.mul Circle.exp.continuous

/-- The genuine inverse angle chart is the restriction of the complete actual circle parametrization. -/
theorem circlePuncturedAngleHomeomorph_symm_coe (a : Circle) (t : Ioo (-Real.pi) Real.pi) :
    ((circlePuncturedAngleHomeomorph a).symm t).val = circleArcParam a t.val := by
  change (Circle.exp Real.pi*a⁻¹)⁻¹ * Circle.exp t.val = _
  simp only [mul_inv_rev,inv_inv,circleArcParam,div_eq_mul_inv]

theorem circle_locallyConnectedSpace : LocallyConnectedSpace Circle := by
  have hs : Function.Surjective Circle.exp := fun u => ⟨Complex.arg (u : ℂ),Circle.exp_arg u⟩
  exact (Circle.isCoveringMap_exp.isQuotientMap hs).isCoinducing.locallyConnectedSpace

/-- Every actual connected open proper circle region avoiding a chosen point is an actual open angle arc. -/
theorem circle_connected_open_eq_actual_arc (a : Circle) {C : Set Circle}
    (hC : IsConnected C) (hCo : IsOpen C) (ha : a ∉ C) :
    ∃ l r : ℝ, -Real.pi ≤ l ∧ l < r ∧ r ≤ Real.pi ∧
      C = circleArcParam a '' Ioo l r := by
  let P : Set Circle := {u | u ≠ a}
  have hPo : IsOpen P := isClosed_singleton.isOpen_compl
  let φ := circlePuncturedAngleHomeomorph a
  let C' : Set P := Subtype.val ⁻¹' C
  have hC' : IsConnected C' := hC.preimage_of_isOpenMap Subtype.val_injective
    hPo.isOpenMap_subtype_val (fun u hu => ⟨⟨u,fun he => ha (he ▸ hu)⟩,rfl⟩)
  have hC'o : IsOpen C' := hCo.preimage continuous_subtype_val
  let A : Set ℝ := Subtype.val '' (φ '' C')
  have hA : IsConnected A := (hC'.image φ φ.continuous.continuousOn).image
    Subtype.val continuous_subtype_val.continuousOn
  have hAo : IsOpen A := isOpen_Ioo.isOpenMap_subtype_val _ (φ.isOpenMap _ hC'o)
  have hAbounds : A ⊆ Ioo (-Real.pi) Real.pi := by rintro _ ⟨t,_ht,rfl⟩; exact t.property
  have hAb : BddBelow A := ⟨-Real.pi,fun _ ht => (hAbounds ht).1.le⟩
  have hAa : BddAbove A := ⟨Real.pi,fun _ ht => (hAbounds ht).2.le⟩
  have he := real_bounded_connected_open_eq_Ioo hA hAo hAb hAa
  have hlr : sInf A < sSup A := by
    have hh := hA.nonempty
    rw [he] at hh
    exact nonempty_Ioo.mp hh
  refine ⟨sInf A,sSup A,le_csInf hA.nonempty (fun _ ht => (hAbounds ht).1.le),hlr,
    csSup_le hA.nonempty (fun _ ht => (hAbounds ht).2.le),?_⟩
  ext u
  constructor
  · intro hu
    let v : P := ⟨u,fun he => ha (he ▸ hu)⟩
    have htA : (φ v).val ∈ A := ⟨φ v,⟨v,hu,rfl⟩,rfl⟩
    refine ⟨(φ v).val,he ▸ htA,?_⟩
    have hh := circlePuncturedAngleHomeomorph_symm_coe a (φ v)
    rw [φ.symm_apply_apply] at hh
    exact hh.symm
  · rintro ⟨t,ht,rfl⟩
    have htA : t ∈ A := he.symm ▸ ht
    obtain ⟨v,⟨x,hx,hφx⟩,hvt⟩ := htA
    have hh := circlePuncturedAngleHomeomorph_symm_coe a (φ x)
    rw [φ.symm_apply_apply] at hh
    rw [←hvt,←hφx,←hh]
    exact hx

/-- Closing a genuine positive open angle arc gives precisely its actual compact closed arc. -/
theorem circleArcParam_closure_image (a : Circle) (l r : ℝ) (hlr : l < r) :
    closure (circleArcParam a '' Ioo l r) = circleArcParam a '' Icc l r := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self)
      ((isCompact_Icc.image (continuous_circleArcParam a)).isClosed)
  · rw [←closure_Ioo hlr.ne]
    exact image_closure_subset_closure_image (continuous_circleArcParam a)


/-- A genuine open circle region with finite actual frontier has finitely many actual connected components. -/
theorem circle_open_finite_frontier_components_finite {U : Set Circle}
    (hU : IsOpen U) (hfin : (frontier U).Finite) :
    ((fun x => connectedComponentIn U x) '' U).Finite := by
  obtain ⟨F,hF,hcover,hpre⟩ := circle_sdiff_finite_preconnected_cover (frontier U) hfin
  let E : Set (Set Circle) := {V ∈ F | V ⊆ U}
  have hEc : U = ⋃ V ∈ E, V := by
    ext x
    constructor
    · intro hxU
      have hxf : x ∉ frontier U := fun hxF =>
        (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hU)) hxF hxU
      have hx : x ∈ (frontier U)ᶜ := hxf
      rw [hcover] at hx
      obtain ⟨V,hVF,hxV⟩ := mem_iUnion₂.mp hx
      have hVsub : V ⊆ U := isPreconnected_subset_open_of_avoids_frontier (hpre V hVF)
        hU (disjoint_left.mpr (fun y hy hyf => by
          have hy' : y ∈ (frontier U)ᶜ := by rw [hcover]; exact mem_iUnion₂.mpr ⟨V,hVF,hy⟩
          exact hy' hyf)) ⟨x,hxV,hxU⟩
      exact mem_iUnion₂.mpr ⟨V,⟨hVF,hVsub⟩,hxV⟩
    · intro hx
      obtain ⟨V,⟨_hVF,hVU⟩,hxV⟩ := mem_iUnion₂.mp hx
      exact hVU hxV
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.finite_connectedComponentIn_image_of_finite_preconnected_cover U E
    (hF.subset (fun _ hV => hV.1)) (by rw [hEc])
    (fun V hV x hx => by rw [hEc]; exact mem_iUnion₂.mpr ⟨V,hV,hx⟩)
    (fun V hV => hpre V hV.1)

/-- A genuine proper open circle region with finite frontier closes to finitely many
actual compact angle arcs; the statement permits a whole-circle closed arc. -/
theorem circle_open_finite_frontier_closed_arc_cover {U : Set Circle}
    (hU : IsOpen U) (hfin : (frontier U).Finite) (hUne : U ≠ univ) :
    ∃ a : Circle, ∃ F : Set (Set Circle), F.Finite ∧ closure U = ⋃ A ∈ F, A ∧
      ∀ A ∈ F, ∃ l r : ℝ, -Real.pi ≤ l ∧ l < r ∧ r ≤ Real.pi ∧
        A = circleArcParam a '' Icc l r ∧ circleArcParam a '' Ioo l r ⊆ U := by
  let : LocallyConnectedSpace Circle := circle_locallyConnectedSpace
  obtain ⟨a,ha⟩ := (Set.ne_univ_iff_exists_notMem U).mp hUne
  let C : Set (Set Circle) := (fun x => connectedComponentIn U x) '' U
  have hC : C.Finite := circle_open_finite_frontier_components_finite hU hfin
  have hcov : U = ⋃ V ∈ C, V := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion₂.mpr ⟨connectedComponentIn U x,⟨x,hx,rfl⟩,mem_connectedComponentIn hx⟩
    · intro hx
      obtain ⟨_,⟨x,hx,rfl⟩,hy⟩ := mem_iUnion₂.mp hx
      exact connectedComponentIn_subset U x hy
  let F := closure '' C
  refine ⟨a,F,hC.image closure,?_,?_⟩
  · change closure U = ⋃ V ∈ closure '' C, V
    rw [biUnion_image,←hC.closure_biUnion (fun V => V),←hcov]
  · rintro A ⟨V,⟨x,hx,rfl⟩,rfl⟩
    have hc : IsConnected (connectedComponentIn U x) := isConnected_connectedComponentIn_iff.mpr hx
    have ho : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
    have hnot : a ∉ connectedComponentIn U x := fun hh => ha (connectedComponentIn_subset U x hh)
    obtain ⟨l,r,hl,hlr,hr,he⟩ := circle_connected_open_eq_actual_arc a hc ho hnot
    refine ⟨l,r,hl,hlr,hr,?_⟩
    refine ⟨?_,?_⟩
    · change closure (connectedComponentIn U x) = circleArcParam a '' Icc l r
      rw [he,circleArcParam_closure_image a l r hlr]
    · rw [←he]
      exact connectedComponentIn_subset U x


theorem circleArcParam_image_full (a : Circle) :
    circleArcParam a '' Icc (-Real.pi) Real.pi = univ := by
  apply eq_univ_of_forall
  intro u
  let v := (a / Circle.exp Real.pi)⁻¹ * u
  refine ⟨Complex.arg (v : ℂ),⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩,?_⟩
  change a / Circle.exp Real.pi * Circle.exp (Complex.arg (v : ℂ)) = u
  rw [Circle.exp_arg]
  exact mul_inv_cancel_left (a / Circle.exp Real.pi) u

/-- The closure of any actual open circle region with finite frontier is a finite union of actual compact angle arcs. -/
theorem circle_open_finite_frontier_closed_arc_cover_all {U : Set Circle}
    (hU : IsOpen U) (hfin : (frontier U).Finite) :
    ∃ a : Circle, ∃ F : Set (Set Circle), F.Finite ∧ closure U = ⋃ A ∈ F, A ∧
      ∀ A ∈ F, ∃ l r : ℝ, -Real.pi ≤ l ∧ l < r ∧ r ≤ Real.pi ∧
        A = circleArcParam a '' Icc l r ∧ circleArcParam a '' Ioo l r ⊆ U := by
  by_cases he : U = univ
  · refine ⟨1,{univ},finite_singleton _,?_,?_⟩
    · simp only [he,closure_univ,mem_singleton_iff,iUnion_iUnion_eq_left]
    · intro A hA
      have hAeq : A = univ := hA
      refine ⟨-Real.pi,Real.pi,le_rfl,by linarith [Real.pi_pos],le_rfl,?_⟩
      refine ⟨by rw [hAeq,circleArcParam_image_full],?_⟩
      rw [he]
      exact subset_univ _
  · exact circle_open_finite_frontier_closed_arc_cover hU hfin he

/-- The actual compact-circle arc parametrization in the original Fuchsian domain carrier. -/
def fuchsianCircleArcParam {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (hR : 0
      < R)
    (a : Circle) (t : ℝ) : P.domain.carrier :=
  (fuchsianMetricCircleHomeomorph P w R hR (circleArcParam a t)).val

/-- The closure of the genuine polygon-circle interior intersection is a finite union
of actual compact circle arcs in the original carrier. -/
theorem fuchsian_polygon_circle_closed_arc_cover
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon P D)
    (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    ∃ a : Circle, ∃ F : Set (Set P.domain.carrier), F.Finite ∧
      closure (D ∩ {x | P.hyperbolicDist w x = R}) = ⋃ A ∈ F, A ∧
      ∀ A ∈ F, ∃ l r : ℝ, -Real.pi ≤ l ∧ l < r ∧ r ≤ Real.pi ∧
        A = fuchsianCircleArcParam P w R hR a '' Icc l r ∧
          fuchsianCircleArcParam P w R hR a '' Ioo l r ⊆ D := by
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let f : Circle → P.domain.carrier := fun u => (e u).val
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  let U := f ⁻¹' D
  have hU : IsOpen U := hD.locallyFinite.fundamental.isOpen.preimage hf
  have hfin : (frontier U).Finite := by
    have hB : (f ⁻¹' frontier D).Finite := by
      apply (fuchsian_polygon_frontier_hyperbolic_circle_inter_finite hD w R).of_injOn
        (f := f) ?_ hinj.injOn
      intro u hu
      exact ⟨hu,(e u).property⟩
    exact hB.subset (hf.frontier_preimage_subset D)
  obtain ⟨a,E,hE,hcov,hprop⟩ := circle_open_finite_frontier_closed_arc_cover_all hU hfin
  have heU : f '' U = D ∩ {x | P.hyperbolicDist w x = R} := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,(e u).property⟩
    · rintro ⟨hxD,hxR⟩
      let u := e.symm ⟨x,hxR⟩
      have he : f u = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hxR⟩)
      exact ⟨u,by change f u ∈ D; rwa [he],he⟩
  let F := (fun V => f '' V) '' E
  refine ⟨a,F,hE.image _,?_,?_⟩
  · rw [←heU,hf.isClosedMap.closure_image_eq_of_continuous hf,hcov]
    change f '' (⋃ V ∈ E, V) = ⋃ A ∈ (fun V => f '' V) '' E, A
    rw [biUnion_image]
    simp only [image_iUnion]
  · rintro A ⟨V,hVE,rfl⟩
    obtain ⟨l,r,hl,hlr,hr,he,hsub⟩ := hprop V hVE
    refine ⟨l,r,hl,hlr,hr,?_⟩
    refine ⟨?_,?_⟩
    · change f '' V = fuchsianCircleArcParam P w R hR a '' Icc l r
      rw [he,image_image]
      rfl
    · rintro _ ⟨t,ht,rfl⟩
      exact hsub ⟨t,ht,rfl⟩


/-- Every actual closed-polygon circle cut is covered by finitely many genuine compact
circle arcs with open interiors in the original polygon, together with the actual finite cut points. -/
theorem fuchsian_closed_polygon_circle_finite_arc_point_cover
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    ∃ a : Circle, ∃ F : Set (Set P.domain.carrier), F.Finite ∧
      (frontier D ∩ {x | P.hyperbolicDist w x = R}).Finite ∧
      closure D ∩ {x | P.hyperbolicDist w x = R} =
        (frontier D ∩ {x | P.hyperbolicDist w x = R}) ∪ ⋃ A ∈ F, A ∧
      ∀ A ∈ F, ∃ l r : ℝ, -Real.pi ≤ l ∧ l < r ∧ r ≤ Real.pi ∧
        A = fuchsianCircleArcParam P w R hR a '' Icc l r ∧
          fuchsianCircleArcParam P w R hR a '' Ioo l r ⊆ D := by
  obtain ⟨a,F,hF,hcov,hprop⟩ := fuchsian_polygon_circle_closed_arc_cover hD w R hR
  let C : Set P.domain.carrier := {x | P.hyperbolicDist w x = R}
  have hC : IsClosed C := by
    apply isClosed_eq _ continuous_const
    change Continuous (fun x => dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate x))
    fun_prop
  have hcl : closure (D ∩ C) ⊆ closure D ∩ C :=
    closure_minimal (fun _ hx => ⟨subset_closure hx.1,hx.2⟩) (isClosed_closure.inter hC)
  refine ⟨a,F,hF,fuchsian_polygon_frontier_hyperbolic_circle_inter_finite hD w R,?_,hprop⟩
  rw [←hcov]
  apply Subset.antisymm
  · rintro x ⟨hxD,hxC⟩
    by_cases hx : x ∈ D
    · exact Or.inr (subset_closure ⟨hx,hxC⟩)
    · exact Or.inl ⟨by rw [hD.locallyFinite.fundamental.isOpen.frontier_eq]; exact ⟨hxD,hx⟩,hxC⟩
  · rintro x (hx | hx)
    · exact ⟨frontier_subset_closure hx.1,hx.2⟩
    · exact hcl hx


/-- A genuine metric circle cut by an actual geodesic away from its nearest-point
radius has a second distinct actual intersection, constructed by true orthogonal reflection. -/
theorem halfPlaneLine_circle_other_intersection (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (w
  x : ℍ) (R : ℝ)
    (hx : x ∈ L.carrier) (hxR : dist w x = R) (hcrit : R ≠ L.pointDist w) :
    ∃ y : ℍ, y ∈ L.carrier ∧ dist w y = R ∧ y ≠ x := by
  let p := L.orthogonalFoot w
  obtain ⟨M,hwM,horth⟩ := L.orthogonalFoot_perpendicular w
  have hML : M.OrthogonalAt L p :=
    ⟨horth.2.1,horth.1,(real_inner_comm _ _).trans horth.2.2⟩
  have hxp : x ≠ p := by
    intro he
    apply hcrit
    calc
      R = dist w x := hxR.symm
      _ = dist w p := congrArg (dist w) he
      _ = L.pointDist w := (L.pointDist_eq_orthogonalFoot w).symm
  refine ⟨M.reflection x,?_,?_,M.reflection_ne_of_perpendicular L p x hML hx hxp⟩
  · rw [←M.reflection_image_of_orthogonalAt L p hML]
    exact mem_image_of_mem M.reflection hx
  · have hd := M.reflection_isometry.dist_eq w x
    rw [(M.reflection_fixed_iff w).mpr hwM] at hd
    exact hd.trans hxR

/-- There are actual positive radii beyond every bound avoiding all original vertices,
elliptic fixed points, and all genuine support-line nearest-point distances. -/
theorem exists_polygon_circle_radius_with_two_point_side_cuts
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (w : P.domain.carrier) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      (∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
        ¬ IsFuchsianPolygonVertex P D x ∧ IsDirichletCenter P x) ∧
      ∀ S : Set P.domain.carrier, IsFuchsianPolygonSide P D S →
        ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine, P.finiteCoordinate '' S ⊆ L.carrier ∧
          R ≠ L.toHalfPlane.pointDist (P.halfPlaneCoordinate w) ∧
          ∀ x : ℍ, x ∈ L.toHalfPlane.carrier → dist (P.halfPlaneCoordinate w) x = R →
            ∃ y : ℍ, y ∈ L.toHalfPlane.carrier ∧ dist (P.halfPlaneCoordinate w) y = R ∧ y ≠ x := by
  classical
  let T := {S : Set P.domain.carrier // IsFuchsianPolygonSide P D S}
  let : Countable T := (fuchsianPolygonSides_countable P D).to_subtype
  let L : T → _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine := fun S => S.property.2.1.2.choose
  have hL (S : T) : P.finiteCoordinate '' S.val ⊆ (L S).carrier := S.property.2.1.2.choose_spec
  let A : Set P.domain.carrier := {x | IsFuchsianPolygonVertex P D x} ∪ fuchsianEllipticPoints P
  have hA : A.Countable := (fuchsianPolygonVertices_countable P D).union (fuchsianEllipticPoints_countable P)
  let B := ((fun x => P.hyperbolicDist w x) '' A) ∪
    range (fun S : T => (L S).toHalfPlane.pointDist (P.halfPlaneCoordinate w))
  have hB : B.Countable := (hA.image _).union (countable_range _)
  obtain ⟨R,hR,hRB⟩ := (hB.dense_compl ℝ).inter_open_nonempty
    (Ioi (max R₀ 0)) isOpen_Ioi nonempty_Ioi
  refine ⟨R,(le_max_left _ _).trans_lt hR,(le_max_right _ _).trans_lt hR,?_,?_⟩
  · intro x hx
    have hxA : x ∉ A := fun hxa => hRB (Or.inl ⟨x,hxa,hx⟩)
    refine ⟨fun hv => hxA (Or.inl hv),?_⟩
    by_contra hc
    exact hxA (Or.inr hc)
  · intro S hS
    have hcrit : R ≠ (L ⟨S,hS⟩).toHalfPlane.pointDist (P.halfPlaneCoordinate w) := by
      intro he
      exact hRB (Or.inr ⟨⟨S,hS⟩,he.symm⟩)
    exact ⟨L ⟨S,hS⟩,hL ⟨S,hS⟩,hcrit,
      fun x hx hxR => halfPlaneLine_circle_other_intersection _ _ x R hx hxR hcrit⟩


/-- At a genuine circle point, the radial vector is not orthogonal to the chord to any second actual circle point. -/
theorem complex_circle_radial_inner_chord_ne (c x y : ℂ) (hEq : ‖x-c‖ = ‖y-c‖) (hyx : y ≠ x) :
    inner ℝ (x-c) (y-x) ≠ 0 := by
  intro he
  have hh := norm_add_sq_real (x-c) (y-x)
  rw [show x-c+(y-x)=y-c by abel,←hEq,he] at hh
  have hn : ‖y-x‖ = 0 := by nlinarith [norm_nonneg (y-x)]
  exact hyx (sub_eq_zero.mp (norm_eq_zero.mp hn))

/-- Two genuine distinct-centered circles sharing a second actual point have independent actual tangents. -/
theorem complex_two_circles_radials_not_parallel (c d x y : ℂ) (hcd : c ≠ d) (hyx : y ≠ x)
    (hc : ‖x-c‖ = ‖y-c‖) (hd : ‖x-d‖ = ‖y-d‖) :
    ¬ ∃ t : ℝ, x-c = t • (x-d) := by
  rintro ⟨t,ht⟩
  have ht1 : t ≠ 1 := by
    intro he
    rw [he,one_smul] at ht
    exact hcd (by linear_combination -ht)
  have hh1 := norm_add_sq_real (x-c) (y-x)
  have hh2 := norm_add_sq_real (x-d) (y-x)
  rw [show x-c+(y-x)=y-c by abel,←hc] at hh1
  rw [show x-d+(y-x)=y-d by abel,←hd] at hh2
  have heq : inner ℝ (x-c) (y-x) = inner ℝ (x-d) (y-x) := by linarith
  have hi := congrArg (fun z : ℂ => inner ℝ z (y-x)) ht
  rw [real_inner_smul_left,heq] at hi
  have hz : (t-1)*inner ℝ (x-d) (y-x) = 0 := by nlinarith only [hi]
  have hzero := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ht1)
  exact complex_circle_radial_inner_chord_ne d x y hd hyx hzero

/-- Away from the genuine nearest-point radius, the actual native geodesic tangent
and actual Euclidean tangent to the genuine hyperbolic circle are linearly independent. -/
theorem halfPlaneLine_metricCircle_tangent_not_parallel (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (w x : ℍ) (R : ℝ)
    (hx : x ∈ L.carrier) (hxR : dist w x = R) (hcrit : R ≠ L.pointDist w) :
    ¬ ∃ t : ℝ, Complex.I*((x : ℂ)-(w.center R : ℂ)) = t • L.tangentAt x := by
  obtain ⟨y,hy,hyR,hyx⟩ := halfPlaneLine_circle_other_intersection L w x R hx hxR hcrit
  have hxc : ‖(x : ℂ)-(w.center R : ℂ)‖ = w.im*Real.sinh R := by
    have hh := UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm] : dist x w = R)
    simpa only [dist_eq_norm] using hh
  have hyc : ‖(y : ℂ)-(w.center R : ℂ)‖ = w.im*Real.sinh R := by
    have hh := UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm] : dist y w = R)
    simpa only [dist_eq_norm] using hh
  have hyx' : (y : ℂ) ≠ (x : ℂ) := fun he => hyx (UpperHalfPlane.ext he)
  cases L with
  | vertical c =>
    rintro ⟨t,ht⟩
    have hrad : (x : ℂ)-(w.center R : ℂ) = (t : ℂ) := by
      apply mul_left_cancel₀ Complex.I_ne_zero
      change Complex.I*((x : ℂ)-(w.center R : ℂ)) = t • Complex.I at ht
      rw [Complex.real_smul] at ht
      convert ht using 1
      ring
    apply complex_circle_radial_inner_chord_ne (w.center R) x y (hxc.trans hyc.symm) hyx'
    rw [hrad,Complex.inner]
    have hxr : x.re = c := hx
    have hyr : y.re = c := hy
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.conj_ofReal,
      Complex.sub_re,UpperHalfPlane.coe_re,hxr,hyr,sub_self,mul_zero,zero_mul]
  | circle c r hr =>
    rintro ⟨t,ht⟩
    have hrad : (x : ℂ)-(w.center R : ℂ) = t • ((x : ℂ)-(c : ℂ)) := by
      apply mul_left_cancel₀ Complex.I_ne_zero
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.tangentAt,mul_smul_comm] using ht
    have hcenter : (w.center R : ℂ) ≠ (c : ℂ) := by
      intro he
      have hh := congrArg Complex.im he
      rw [UpperHalfPlane.coe_im,UpperHalfPlane.center_im,Complex.ofReal_im] at hh
      exact (mul_pos w.im_pos (Real.cosh_pos R)).ne' hh
    have hxL : ‖(x : ℂ)-(c : ℂ)‖ = r := hx
    have hyL : ‖(y : ℂ)-(c : ℂ)‖ = r := hy
    exact complex_two_circles_radials_not_parallel (w.center R) c x y hcenter hyx'
      (hxc.trans hyc.symm) (hxL.trans hyL.symm) ⟨t,hrad⟩


/-- True positive metric circles transverse to every actual polygon support geodesic,
avoiding all actual vertices and elliptic fixed points, occur beyond every prescribed radius. -/
theorem exists_polygon_circle_radius_transverse_to_sides
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (w : P.domain.carrier) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      (∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
        ¬ IsFuchsianPolygonVertex P D x ∧ IsDirichletCenter P x) ∧
      ∀ S : Set P.domain.carrier, IsFuchsianPolygonSide P D S →
        ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine, P.finiteCoordinate '' S ⊆ L.carrier ∧
          ∀ x : ℍ, x ∈ L.toHalfPlane.carrier → dist (P.halfPlaneCoordinate w) x = R →
            ¬ ∃ t : ℝ, Complex.I*((x : ℂ)-((P.halfPlaneCoordinate w).center R : ℂ)) =
              t • L.toHalfPlane.tangentAt x := by
  obtain ⟨R,hR,hRpos,havoid,hside⟩ := exists_polygon_circle_radius_with_two_point_side_cuts P D w R₀
  refine ⟨R,hR,hRpos,havoid,?_⟩
  intro S hS
  obtain ⟨L,hL,hcrit,_hsecond⟩ := hside S hS
  exact ⟨L,hL,fun x hx hxR => halfPlaneLine_metricCircle_tangent_not_parallel
    L.toHalfPlane (P.halfPlaneCoordinate w) x R hx hxR hcrit⟩

end LowDimensionalTopology.Geometry.Fuchsian
