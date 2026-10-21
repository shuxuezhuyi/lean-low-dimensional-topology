/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HalfPlanes
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Every point has a genuine local chart onto a hyperbolic ball of the same radius. -/
structure UniformHyperbolicBallCharts {Y : Type*} [TopologicalSpace Y]
    (p : Y→ℍ) (ε : ℝ) where
  chart : Y→OpenPartialHomeomorph Y ℍ
  center_mem : ∀y,y∈(chart y).source
  target_eq : ∀y,(chart y).target=Metric.ball (p y) ε
  map_eq : ∀y,EqOn (chart y) p (chart y).source

variable {Y : Type*} [TopologicalSpace Y] {p : Y→ℍ} {ε : ℝ}

/-- Uniform ball charts in particular establish local homeomorphy of the given map. -/
theorem UniformHyperbolicBallCharts.isLocalHomeomorph
    (h : UniformHyperbolicBallCharts p ε) : IsLocalHomeomorph p := by
  exact IsLocalHomeomorph.mk p (fun y=>⟨h.chart y,h.center_mem y,fun z hz=>(h.map_eq y hz).symm⟩)

/-- The actual inverse branch projects to its input throughout its actual ball target. -/
theorem UniformHyperbolicBallCharts.branch_projects
    (h : UniformHyperbolicBallCharts p ε) (y : Y) {z : ℍ}
    (hz : z∈Metric.ball (p y) ε) : p ((h.chart y).symm z)=z := by
  have ht : z∈(h.chart y).target:=by rwa [h.target_eq]
  rw [←h.map_eq y ((h.chart y).map_target ht)]
  exact (h.chart y).right_inv ht

/-- At its own center an actual inverse branch returns the specified original point. -/
theorem UniformHyperbolicBallCharts.branch_center
    (h : UniformHyperbolicBallCharts p ε) (y : Y) : (h.chart y).symm (p y)=y := by
  rw [←h.map_eq y (h.center_mem y)]
  exact (h.chart y).left_inv (h.center_mem y)

/-- Every pairwise intersection of the genuine hyperbolic metric balls is preconnected. -/
theorem hyperbolic_ball_inter_isPreconnected (a b : ℍ) (r s : ℝ) :
    IsPreconnected (Metric.ball a r∩Metric.ball b s) := by
  have hc : HConvex (Metric.ball a r∩Metric.ball b s) := by
    intro z hz w hw q hq
    exact ⟨hConvex_metric_ball a r z hz.1 w hw.1 hq,
      hConvex_metric_ball b s z hz.2 w hw.2 hq⟩
  exact hc.isPreconnected

/-- Hausdorffness and actual local injectivity force two inverse branches that meet
once to agree throughout the connected intersection of their ball targets. -/
theorem UniformHyperbolicBallCharts.branch_eqOn [T2Space Y]
    (h : UniformHyperbolicBallCharts p ε) (y z : Y) {a : ℍ}
    (ha : a∈Metric.ball (p y) ε∩Metric.ball (p z) ε)
    (he : (h.chart y).symm a=(h.chart z).symm a) :
    EqOn (h.chart y).symm (h.chart z).symm
      (Metric.ball (p y) ε∩Metric.ball (p z) ε) := by
  apply (T2Space.isSeparatedMap p).eqOn_of_comp_eqOn
    h.isLocalHomeomorph.isLocallyInjective (hyperbolic_ball_inter_isPreconnected _ _ _ _)
    ((h.chart y).continuousOn_invFun.mono (by rw [h.target_eq];exact inter_subset_left))
    ((h.chart z).continuousOn_invFun.mono (by rw [h.target_eq];exact inter_subset_right))
    (fun w hw=>(h.branch_projects y hw.1).trans (h.branch_projects z hw.2).symm) ha he

/-- A uniform chart radius rules out omitted limit points of the actual image. -/
theorem UniformHyperbolicBallCharts.isClosed_range
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) : IsClosed (range p) := by
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨_,⟨y,rfl⟩,hy⟩:=(Metric.mem_closure_iff.mp hx) ε hε
  exact ⟨(h.chart y).symm x,h.branch_projects y (by simpa only [Metric.mem_ball,dist_comm] using hy)⟩

/-- Uniform charts make the map onto the connected native hyperbolic plane;
no surjectivity or completeness hypothesis is used. -/
theorem UniformHyperbolicBallCharts.surjective [Nonempty Y]
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) : Function.Surjective p := by
  have hopen : IsOpen (range p):=h.isLocalHomeomorph.isOpenMap.isOpen_range
  have hclosed:=h.isClosed_range hε
  have hne : (range p).Nonempty:=⟨p (Classical.arbitrary Y),mem_range_self _⟩
  exact range_eq_univ.mp (IsClopen.eq_univ ⟨hclosed,hopen⟩ hne)

/-- Actual local injectivity makes each original point fiber discrete. -/
theorem UniformHyperbolicBallCharts.fiber_discrete
    (h : UniformHyperbolicBallCharts p ε) (x : ℍ) : DiscreteTopology (p ⁻¹' {x}) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro y
  have he : (Subtype.val : (p ⁻¹' {x})→Y) ⁻¹' (h.chart y.val).source={y} := by
    ext z
    constructor
    · intro hz
      apply Subtype.ext
      apply (h.chart y.val).injOn hz (h.center_mem y.val)
      rw [h.map_eq y.val hz,h.map_eq y.val (h.center_mem y.val)]
      exact z.property.trans y.property.symm
    · rintro rfl
      exact h.center_mem _
  rw [←he]
  exact (h.chart y.val).open_source.preimage continuous_subtype_val

/-- A branch recentered over a nearby target point recovers every point of the
original chart, because the genuine two-ball intersection is connected. -/
theorem UniformHyperbolicBallCharts.branch_recenter [T2Space Y]
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) (z : Y) {x : ℍ}
    (hx : x∈Metric.ball (p z) ε) :
    (h.chart ((h.chart z).symm x)).symm (p z)=z := by
  let y:=(h.chart z).symm x
  have hpy : p y=x:=h.branch_projects z hx
  have hcenter : x∈Metric.ball (p y) ε:=by rw [hpy];exact Metric.mem_ball_self hε
  have he : (h.chart z).symm x=(h.chart y).symm x := by
    have hyc:=h.branch_center y
    rw [hpy] at hyc
    exact hyc.symm
  have heq:=h.branch_eqOn z y ⟨hx,hcenter⟩ he
  have hz : p z∈Metric.ball (p z) ε∩Metric.ball (p y) ε := by
    refine ⟨Metric.mem_ball_self hε,?_⟩
    rw [hpy]
    simpa only [Metric.mem_ball,dist_comm] using hx
  exact (heq hz).symm.trans (h.branch_center z)

/-- A map on a product is open whenever every fixed-second-coordinate section is open. -/
theorem isOpenMap_of_open_sections {A B I : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace I] (f : A×I→B)
    (hf : ∀i,IsOpenMap (fun a=>f (a,i))) : IsOpenMap f := by
  intro U hU
  have he : f '' U=⋃i,(fun a=>f (a,i)) '' ((fun a=>(a,i)) ⁻¹' U) := by
    ext b
    simp only [mem_image,mem_iUnion,mem_preimage]
    constructor
    · rintro ⟨⟨a,i⟩,ha,rfl⟩
      exact ⟨i,a,ha,rfl⟩
    · rintro ⟨i,a,ha,rfl⟩
      exact ⟨(a,i),ha,rfl⟩
  rw [he]
  exact isOpen_iUnion (fun i=>hf i _ (hU.preimage (continuous_id.prodMk continuous_const)))

/-- Uniform-radius ball charts evenly cover the full target ball. The proof constructs
all actual sheets, proves they are disjoint, and exhausts the full original preimage. -/
theorem UniformHyperbolicBallCharts.evenlyCovered [T2Space Y]
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) (x : ℍ) :
    IsEvenlyCovered p x (p ⁻¹' {x}) := by
  classical
  let B:=Metric.ball x ε
  let I:=p ⁻¹' {x}
  let : DiscreteTopology I:=h.fiber_discrete x
  let F:B×I→Y:=fun a=>(h.chart a.2.val).symm a.1.val
  have htarget (i : I) : (h.chart i.val).target=B := by
    rw [h.target_eq,i.property]
  have hsection (i : I) : IsOpenEmbedding (fun b : B=>(h.chart i.val).symm b.val) := by
    have H:=(h.chart i.val).symm.isOpenEmbedding_restrict
    rw [show (h.chart i.val).symm.source=B from htarget i] at H
    exact H
  have hproj (a : B×I) : p (F a)=a.1.val := by
    apply h.branch_projects
    rw [a.2.property]
    exact a.1.property
  have hcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨b,i⟩
    rw [continuousAt_prod_of_discrete_right]
    exact (hsection i).continuous.continuousAt
  have hopen : IsOpenMap F:=isOpenMap_of_open_sections F (fun i=>(hsection i).isOpenMap)
  have hinj : Function.Injective F := by
    rintro ⟨a,i⟩ ⟨b,j⟩ he
    have hab : a=b:=Subtype.ext ((hproj (a,i)).symm.trans ((congrArg p he).trans (hproj (b,j))))
    subst b
    have hat : a.val∈Metric.ball (p i.val) ε∩Metric.ball (p j.val) ε := by
      rw [i.property,j.property]
      exact ⟨a.property,a.property⟩
    have heq:=h.branch_eqOn i.val j.val hat he
    have hxt : x∈Metric.ball (p i.val) ε∩Metric.ball (p j.val) ε := by
      rw [i.property,j.property]
      exact ⟨Metric.mem_ball_self hε,Metric.mem_ball_self hε⟩
    have hij : i=j := by
      apply Subtype.ext
      have hh:=heq hxt
      rw [←i.property] at hh
      rw [h.branch_center] at hh
      rw [i.property,←j.property,h.branch_center] at hh
      exact hh
    exact Prod.ext rfl hij
  let G:B×I→p ⁻¹' B:=fun a=>⟨F a,by rw [mem_preimage,hproj];exact a.1.property⟩
  have hGsurj : Function.Surjective G := by
    intro z
    have hzmem : p z.val∈Metric.ball x ε:=z.property
    have hx : x∈Metric.ball (p z.val) ε:=by simpa only [Metric.mem_ball,dist_comm] using hzmem
    let i:I:=⟨(h.chart z.val).symm x,h.branch_projects z.val hx⟩
    refine ⟨(⟨p z.val,z.property⟩,i),?_⟩
    apply Subtype.ext
    exact h.branch_recenter hε z.val hx
  have hGinj : Function.Injective G:=fun a b he=>hinj (congrArg Subtype.val he)
  have hGhome : IsHomeomorph G:=⟨hcont.subtype_mk _,hopen.subtype_mk _,hGinj,hGsurj⟩
  let E:=hGhome.homeomorph G
  refine ⟨inferInstance,B,Metric.mem_ball_self hε,Metric.isOpen_ball,
    h.isLocalHomeomorph.continuous.isOpen_preimage _ Metric.isOpen_ball,E.symm,?_⟩
  intro z
  have he : G (E.symm z)=z:=E.apply_symm_apply z
  exact (hproj (E.symm z)).symm.trans (congrArg (fun q : p ⁻¹' B=>p q.val) he)

/-- A uniform positive native-ball chart radius proves the actual covering property;
no covering or completeness assumption is added. -/
theorem UniformHyperbolicBallCharts.isCoveringMap [T2Space Y]
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) : IsCoveringMap p :=
  h.evenlyCovered hε

/-- The native hyperbolic plane is simply connected in its actual topology. -/
theorem hyperbolicPlane_simplyConnectedSpace : SimplyConnectedSpace ℍ := by
  let : ContractibleSpace (Metric.ball (0 : ℂ) 1):=Metric.contractibleSpace_ball (by norm_num)
  let : SimplyConnectedSpace Complex.UnitDisc:=inferInstanceAs
    (SimplyConnectedSpace (Metric.ball (0 : ℂ) 1))
  exact cayleyHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance

/-- Uniform charts onto fixed-radius hyperbolic balls determine a genuine global
homeomorphism from a connected Hausdorff domain. No surjectivity, completeness,
covering, or global tessellation assumption occurs in the hypotheses. -/
theorem UniformHyperbolicBallCharts.isHomeomorph [T2Space Y] [ConnectedSpace Y]
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) : IsHomeomorph p := by
  let cov:=h.isCoveringMap hε
  let : SimplyConnectedSpace ℍ:=hyperbolicPlane_simplyConnectedSpace
  let y₀:=Classical.arbitrary Y
  obtain ⟨F,⟨hF₀,hFp⟩,_⟩:=cov.existsUnique_continuousMap_lifts
    (ContinuousMap.id ℍ) (p y₀) y₀ rfl
  have hleft : (F : ℍ→Y)∘p=id := by
    apply cov.eq_of_comp_eq (F.continuous.comp cov.continuous) continuous_id
      (funext fun y=>congrFun hFp (p y)) y₀ hF₀
  refine ⟨cov.continuous,cov.isOpenMap,?_,?_⟩
  · intro y z he
    calc y=F (p y):=(congrFun hleft y).symm
         _=F (p z):=congrArg F he
         _=z:=congrFun hleft z
  · intro x
    exact ⟨F x,congrFun hFp x⟩

/-- The bundled homeomorphism has exactly the original map as its underlying function. -/
def UniformHyperbolicBallCharts.homeomorph [T2Space Y] [ConnectedSpace Y]
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) : Y≃ₜℍ :=
  IsHomeomorph.homeomorph p (h.isHomeomorph hε)

theorem UniformHyperbolicBallCharts.homeomorph_apply [T2Space Y] [ConnectedSpace Y]
    (h : UniformHyperbolicBallCharts p ε) (hε : 0<ε) (y : Y) : h.homeomorph hε y=p y := rfl

/-- The unbundled form directly consumes genuine uniform charts in a developing-space
construction; both global conclusions are derived, not assumed. -/
theorem uniform_hyperbolic_charts_covering_homeomorph [T2Space Y] [ConnectedSpace Y]
    (hε : 0<ε) (hc : ∀y:Y,∃e : OpenPartialHomeomorph Y ℍ,
      y∈e.source ∧ e.target=Metric.ball (p y) ε ∧ EqOn e p e.source) :
    IsCoveringMap p ∧ IsHomeomorph p := by
  classical
  choose e hmem htarget heq using hc
  let h:UniformHyperbolicBallCharts p ε:=⟨e,hmem,htarget,heq⟩
  exact ⟨h.isCoveringMap hε,h.isHomeomorph hε⟩

end LowDimensionalTopology.Geometry.Hyperbolic
