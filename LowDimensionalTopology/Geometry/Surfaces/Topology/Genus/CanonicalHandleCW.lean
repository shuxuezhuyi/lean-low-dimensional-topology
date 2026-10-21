/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleSeparation
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.LocalAtTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter Topology
namespace LowDimensionalTopology.Geometry.Surfaces.HandleCW
open LowDimensionalTopology.Geometry.Surfaces.HandleSeparation

theorem continuousOn_inverse_of_closedMap_unique_fibers
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X→Y} {g : Y→X} {s : Set Y} (hf : IsClosedMap f)
    (hfg : ∀y∈s,f (g y)=y)
    (huniq : ∀y∈s,∀x,f x=y→x=g y) : ContinuousOn g s := by
  intro y hy
  show Tendsto g (𝓝[s] y) (𝓝 (g y))
  rw [tendsto_def]
  intro U hU
  have he : ∀ᶠ b in 𝓝 y,∀x∈f⁻¹' {b},x∈U :=
    hf.eventually_nhds_fiber y (fun x hx => by
      have hxy : x=g y := huniq y hy x hx
      rw [hxy]
      exact hU)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with b hb hbs
  exact hb (g b) (hfg b hbs)

theorem sidePoint_norm_one {g : ℕ} (d : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side g) (t :
  unitInterval) :
    ‖(_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint d
      t).val‖=1 := _root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint_norm _

theorem vertex_norm_one {g : ℕ} {z : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc} (hz : z∈_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.vertices g) : ‖z.val‖=1 := by
  rcases hz with ⟨d,rfl⟩|⟨d,rfl⟩ <;> exact sidePoint_norm_one d _

theorem sideRelated_norm_one {g : ℕ} {z w : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc} (h :
  _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sideRelated g z w) :
    ‖z.val‖=1 ∧ ‖w.val‖=1 := by
  obtain ⟨d,t,rfl,rfl⟩:=h
  exact ⟨sidePoint_norm_one d t,sidePoint_norm_one _ _⟩

theorem quotient_interior_fiber_singleton {g : ℕ} {z w :
  _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc}
    (hz : ‖z.val‖<1)
    (he : Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) w=Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) z) : w=z := by
  rcases (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.quotient_eq_iff_closedRelation g w
    z).mp he with h|h|h
  · exact h
  · exact False.elim ((ne_of_lt hz) (sideRelated_norm_one h).2)
  · exact False.elim ((ne_of_lt hz) (vertex_norm_one h.2))

theorem quotient_injOn_interior (g : ℕ) :
    InjOn (Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)) {z : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc|‖z.val‖<1} := by
  intro z hz w _ he
  exact (quotient_interior_fiber_singleton hz he.symm).symm

theorem quotient_projection_closedMap (g : ℕ) :
    IsClosedMap (Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)) := by
  let : T2Space (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
    g)):=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.canonicalHandleQuotientT2 g
  exact continuous_quot_mk.isClosedMap

theorem quotient_out_projection_interior {g : ℕ} {z :
  _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc} (hz : ‖z.val‖<1) :
    (Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) z).out=z :=
  quotient_interior_fiber_singleton hz (Quot.out_eq _)

theorem quotient_out_continuousOn_interior (g : ℕ) :
    ContinuousOn (Quot.out : Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
      g)→_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc)
      (Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) '' {z : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc|‖z.val‖<1}) := by
  apply continuousOn_inverse_of_closedMap_unique_fibers (quotient_projection_closedMap g)
    (fun q _ => Quot.out_eq q)
  rintro q ⟨z,hz,rfl⟩ w hw
  exact (quotient_interior_fiber_singleton hz hw).trans
    (quotient_out_projection_interior hz).symm

def closedDiscClamp (z : ℂ) : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc :=
  ⟨(max 1 ‖z‖)⁻¹ • z,mem_closedBall_zero_iff.mpr (by
    have hm : 0<max 1 ‖z‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hm.le)]
    exact (inv_mul_le_iff₀ hm).mpr (by simpa only [mul_one] using (le_max_right (1:ℝ) ‖z‖)))⟩

theorem closedDiscClamp_continuous : Continuous closedDiscClamp := by
  apply Continuous.subtype_mk
  exact (((continuous_const.max continuous_norm).inv₀
    (fun z => ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left 1 ‖z‖)))).smul continuous_id)

theorem closedDiscClamp_eq_of_norm_le {z : ℂ} (hz : ‖z‖≤1) :
    (closedDiscClamp z).val=z := by
  change (max 1 ‖z‖)⁻¹ • z=z
  rw [max_eq_left hz,inv_one,one_smul]

theorem diamondSquareAffine_mem_open_square_iff (z : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.diamondSquareAffine z∈Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 ↔
      _root_.LowDimensionalTopology.Geometry.Surfaces.complexDiamondSeminorm z<1 := by
  change (0<(1-z.re+z.im)/2 ∧ (1-z.re+z.im)/2<1) ∧
    (0<(1-z.re-z.im)/2 ∧ (1-z.re-z.im)/2<1) ↔ |z.re|+|z.im|<1
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
    rcases le_total 0 z.re with hx|hx <;> rcases le_total 0 z.im with hy|hy <;>
      simp only [abs_of_nonneg,abs_of_nonpos,hx,hy] <;> linarith
  · intro hz
    have hx:=le_abs_self z.re
    have hnx:=neg_le_abs z.re
    have hy:=le_abs_self z.im
    have hny:=neg_le_abs z.im
    constructor <;> constructor <;> linarith

def cubeSquareAffine : (Fin 2→ℝ)≃ₜℝ×ℝ where
  toFun v:=((v 0+1)/2,(v 1+1)/2)
  invFun w:=![2*w.1-1,2*w.2-1]
  left_inv v:=by funext i;fin_cases i <;> dsimp <;> ring
  right_inv w:=by apply Prod.ext <;> dsimp <;> ring
  continuous_toFun:=by fun_prop
  continuous_invFun:=by fun_prop

theorem cubeSquareAffine_apply (v : Fin 2→ℝ) :
    cubeSquareAffine v=((v 0+1)/2,(v 1+1)/2) := rfl

def cubeDiscHomeomorph : (Fin 2→ℝ)≃ₜℂ :=
  cubeSquareAffine.trans (_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph.trans
    _root_.LowDimensionalTopology.Geometry.Surfaces.diamondSquareAffine).symm

theorem cubeDiscHomeomorph_square_coordinates (v : Fin 2→ℝ) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.diamondSquareAffine (_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph (cubeDiscHomeomorph v))=
      cubeSquareAffine v := by
  change (_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph.trans
    _root_.LowDimensionalTopology.Geometry.Surfaces.diamondSquareAffine)
    ((_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph.trans
      _root_.LowDimensionalTopology.Geometry.Surfaces.diamondSquareAffine).symm (cubeSquareAffine v))=_
  exact Homeomorph.apply_symm_apply _ _

theorem cubeDiscHomeomorph_openBall_iff (v : Fin 2→ℝ) :
    ‖cubeDiscHomeomorph v‖<1 ↔ v∈ball 0 1 := by
  have hh:=diamondSquareAffine_mem_open_square_iff
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph (cubeDiscHomeomorph v))
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph_gauge,cubeDiscHomeomorph_square_coordinates] at hh
  rw [←hh,ball_pi _ (by norm_num : (0:ℝ)<1)]
  simp only [cubeSquareAffine_apply,Set.mem_prod,mem_Ioo,
    Set.mem_pi,mem_univ,forall_const,Pi.zero_apply,mem_ball,Real.dist_eq,sub_zero,abs_lt,
    Fin.forall_fin_two]
  constructor <;> rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ <;> constructor <;> constructor <;> linarith

theorem cubeDiscHomeomorph_closedBall_iff (v : Fin 2→ℝ) :
    ‖cubeDiscHomeomorph v‖≤1 ↔ v∈closedBall 0 1 := by
  have hh:=_root_.LowDimensionalTopology.Geometry.Surfaces.diamondSquareAffine_mem_square_iff
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph (cubeDiscHomeomorph v))
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.discDiamondHomeomorph_gauge,cubeDiscHomeomorph_square_coordinates] at hh
  rw [←hh,closedBall_pi _ (by norm_num : (0:ℝ)≤1)]
  simp only [cubeSquareAffine_apply,Set.mem_prod,mem_Icc,
    Set.mem_pi,mem_univ,forall_const,Pi.zero_apply,mem_closedBall,Real.dist_eq,sub_zero,abs_le,
    Fin.forall_fin_two]
  constructor <;> rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ <;> constructor <;> constructor <;> linarith

def topCellMap (g : ℕ) (v : Fin 2→ℝ) : Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) :=
  Quot.mk _ (closedDiscClamp (cubeDiscHomeomorph v))

theorem topCellMap_continuous (g : ℕ) : Continuous (topCellMap g) :=
  continuous_quot_mk.comp (closedDiscClamp_continuous.comp cubeDiscHomeomorph.continuous)

theorem topCellMap_interior_norm {v : Fin 2→ℝ} (hv : v∈ball 0 1) :
    ‖(closedDiscClamp (cubeDiscHomeomorph v)).val‖<1 := by
  have hh:=(cubeDiscHomeomorph_openBall_iff v).mpr hv
  rw [closedDiscClamp_eq_of_norm_le hh.le]
  exact hh

/-- The genuine two-cell uses the original quotient and the actual max-norm square. -/
def topCell (g : ℕ) : PartialEquiv (Fin 2→ℝ) (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
  g)) where
  toFun:=topCellMap g
  invFun q:=cubeDiscHomeomorph.symm q.out.val
  source:=ball 0 1
  target:=Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) '' {z :
    _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc|‖z.val‖<1}
  map_source' v hv:=⟨closedDiscClamp (cubeDiscHomeomorph v),topCellMap_interior_norm hv,rfl⟩
  map_target':=by
    rintro q ⟨z,hz,rfl⟩
    rw [quotient_out_projection_interior hz]
    apply (cubeDiscHomeomorph_openBall_iff _).mp
    rw [Homeomorph.apply_symm_apply]
    exact hz
  left_inv':=by
    intro v hv
    rw [show topCellMap g v=Quot.mk _ (closedDiscClamp (cubeDiscHomeomorph v)) from rfl,
      quotient_out_projection_interior (topCellMap_interior_norm hv),
      closedDiscClamp_eq_of_norm_le ((cubeDiscHomeomorph_openBall_iff v).mpr hv).le,
      Homeomorph.symm_apply_apply]
  right_inv':=by
    rintro q ⟨z,hz,rfl⟩
    rw [quotient_out_projection_interior hz]
    change Quot.mk _ (closedDiscClamp (cubeDiscHomeomorph (cubeDiscHomeomorph.symm z.val)))=_
    rw [Homeomorph.apply_symm_apply]
    congr 1
    exact Subtype.ext (closedDiscClamp_eq_of_norm_le hz.le)

theorem topCell_source (g : ℕ) : (topCell g).source=ball 0 1 := rfl

theorem topCell_continuousOn (g : ℕ) : ContinuousOn (topCell g) (closedBall 0 1) :=
  (topCellMap_continuous g).continuousOn

theorem topCell_symm_continuousOn (g : ℕ) :
    ContinuousOn (topCell g).symm (topCell g).target :=
  cubeDiscHomeomorph.symm.continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn (quotient_out_continuousOn_interior g))

theorem topCell_closedBall_image (g : ℕ) :
    topCell g '' closedBall 0 1=univ := by
  apply eq_univ_of_forall
  intro q
  induction q using Quot.inductionOn with
  | _ z =>
    refine ⟨cubeDiscHomeomorph.symm z.val,?_,?_⟩
    · apply (cubeDiscHomeomorph_closedBall_iff _).mp
      rw [Homeomorph.apply_symm_apply]
      exact mem_closedBall_zero_iff.mp z.property
    · change Quot.mk _ (closedDiscClamp (cubeDiscHomeomorph (cubeDiscHomeomorph.symm z.val)))=_
      rw [Homeomorph.apply_symm_apply]
      congr 1
      exact Subtype.ext (closedDiscClamp_eq_of_norm_le (mem_closedBall_zero_iff.mp z.property))

def vertexCell (g : ℕ) : PartialEquiv (Fin 0→ℝ) (Quot
  (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)) where
  toFun _:=_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0
  invFun _:=0
  source:=ball 0 1
  target:={_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0}
  map_source' _ _:=rfl
  map_target' _ _:=by simp
  left_inv' v _:=by funext i;exact i.elim0
  right_inv' _ h:=h.symm

theorem vertexCell_continuousOn (g : ℕ) :
    ContinuousOn (vertexCell g) (closedBall 0 1) := continuous_const.continuousOn

theorem vertexCell_symm_continuousOn (g : ℕ) :
    ContinuousOn (vertexCell g).symm (vertexCell g).target := continuous_const.continuousOn

theorem quotient_core_side_fiber {g : ℕ} (d : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side
  g) (t : unitInterval)
    (ht : 0<t.val ∧ t.val<1) {w : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc}
    (he : Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) w=Quot.mk _
      (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint d t)) :
    w=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint d t ∨ w=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.mate d) (unitInterval.symm t) := by
  rcases (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.quotient_eq_iff_closedRelation g w
    (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint d t)).mp he with h|h|h
  · exact Or.inl h
  · obtain ⟨e,u,hzu,hw⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sideRelated_symm h
    obtain ⟨hde,htu⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_core_unique d e t u ht hzu
    rw [←hde,←htu] at hw
    exact Or.inr hw
  · have hh:=(_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_vertex_iff d t).mp h.2
    rcases hh with rfl|rfl <;> norm_num at ht

abbrev Edge (g : ℕ) := Fin g×Fin 2

def edgeSide {g : ℕ} (d : Edge g) : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side g :=
  (d.1,⟨d.2.val,lt_trans d.2.isLt (by norm_num : 2<4)⟩)

theorem edgeSide_injective (g : ℕ) : Function.Injective (edgeSide (g:=g)) := by
  intro d e he
  apply Prod.ext
  · exact congrArg (fun x : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side g => x.1) he
  · apply Fin.ext
    exact congrArg (fun x : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side g => x.2.val) he

theorem edgeSide_ne_mate {g : ℕ} (d e : Edge g) : edgeSide d≠_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.mate (edgeSide e) := by
  intro he
  have hh:=congrArg (fun x : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side g => x.2) he
  rcases d with ⟨i,j⟩
  rcases e with ⟨k,l⟩
  fin_cases j <;> fin_cases l <;> norm_num [edgeSide,_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.mate] at hh

theorem edge_core_quotient_fiber {g : ℕ} (d e : Edge g) (t u : unitInterval)
    (ht : 0<t.val ∧ t.val<1)
    (he : Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)
      (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide e) u)=
      Quot.mk _ (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide d) t)) : e=d ∧ u=t := by
  rcases quotient_core_side_fiber (edgeSide d) t ht he with h|h
  · obtain ⟨hde,htu⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_core_unique (edgeSide
    d) (edgeSide e) t u ht h.symm
    exact ⟨((edgeSide_injective g) hde).symm,htu.symm⟩
  · have ht' : 0<(unitInterval.symm t).val ∧ (unitInterval.symm t).val<1 := by
      change 0<1-t.val ∧ 1-t.val<1
      constructor <;> linarith only [ht.1,ht.2]
    have hh:=(_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_core_unique
      (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.mate (edgeSide d)) (edgeSide e)
      (unitInterval.symm t) u ht' h.symm).1
    exact ((edgeSide_ne_mate e d) hh.symm).elim

def edgeIntervalParam (v : Fin 1→ℝ) : unitInterval :=
  Set.projIcc 0 1 (by norm_num) ((v 0+1)/2)

theorem edgeIntervalParam_continuous : Continuous edgeIntervalParam :=
  continuous_projIcc.comp (by fun_prop)

theorem edgeIntervalParam_eq_of_closedBall {v : Fin 1→ℝ} (hv : v∈closedBall 0 1) :
    (edgeIntervalParam v).val=(v 0+1)/2 := by
  have hb : |v 0|≤1 := by
    exact (norm_le_pi_norm v 0).trans (mem_closedBall_zero_iff.mp hv)
  rw [edgeIntervalParam,Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1)
    (show (v 0+1)/2∈Icc (0:ℝ) 1 from
    ⟨by linarith only [(abs_le.mp hb).1],by linarith only [(abs_le.mp hb).2]⟩)]

theorem edgeIntervalParam_mem_Ioo {v : Fin 1→ℝ} (hv : v∈ball 0 1) :
    0<(edgeIntervalParam v).val ∧ (edgeIntervalParam v).val<1 := by
  have hb : |v 0|<1 := (norm_le_pi_norm v 0).trans_lt (mem_ball_zero_iff.mp hv)
  rw [edgeIntervalParam_eq_of_closedBall (ball_subset_closedBall hv)]
  constructor <;> linarith only [(abs_lt.mp hb).1,(abs_lt.mp hb).2]

def edgeCellMap {g : ℕ} (d : Edge g) (v : Fin
  1→ℝ) : Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) :=
  Quot.mk _ (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide d) (edgeIntervalParam
    v))

theorem edgeCellMap_continuous {g : ℕ} (d : Edge g) : Continuous (edgeCellMap d) :=
  continuous_quot_mk.comp ((_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_continuous
    _).comp edgeIntervalParam_continuous)

theorem edgeCellMap_injOn {g : ℕ} (d : Edge g) : InjOn (edgeCellMap d) (ball 0 1) := by
  intro v hv w hw he
  have hh:=(edge_core_quotient_fiber d d (edgeIntervalParam v) (edgeIntervalParam w)
    (edgeIntervalParam_mem_Ioo hv) he.symm).2
  have hval:=congrArg Subtype.val hh
  rw [edgeIntervalParam_eq_of_closedBall (ball_subset_closedBall hv),
    edgeIntervalParam_eq_of_closedBall (ball_subset_closedBall hw)] at hval
  funext i
  fin_cases i
  change v 0=w 0
  linarith only [hval]

def edgeCell {g : ℕ} (d : Edge g) :
    PartialEquiv (Fin 1→ℝ) (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)) :=
  (edgeCellMap_injOn d).toPartialEquiv (edgeCellMap d) (ball 0 1)

theorem edgeCell_source {g : ℕ} (d : Edge g) : (edgeCell d).source=ball 0 1 := rfl

theorem edgeCell_continuousOn {g : ℕ} (d : Edge g) :
    ContinuousOn (edgeCell d) (closedBall 0 1) := (edgeCellMap_continuous d).continuousOn

theorem edgeCell_symm_continuousOn {g : ℕ} (d : Edge g) :
    ContinuousOn (edgeCell d).symm (edgeCell d).target := by
  let : T2Space (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
    g)):=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.canonicalHandleQuotientT2 g
  let e:=edgeCell d
  let F : unitInterval→Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g):=
    fun t=>Quot.mk _ (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide d) t)
  let G : Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)→unitInterval:=
    fun q=>edgeIntervalParam (e.symm q)
  have hF : Continuous F:=continuous_quot_mk.comp (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_continuous _)
  have hFG : ∀q∈e.target,F (G q)=q := by
    intro q hq
    exact e.right_inv hq
  have hG : ContinuousOn G e.target := by
    apply continuousOn_inverse_of_closedMap_unique_fibers hF.isClosedMap hFG
    intro q hq t ht
    have hv : e.symm q∈ball 0 1:=e.map_target hq
    have hh:=edge_core_quotient_fiber d d (G q) t (edgeIntervalParam_mem_Ioo hv)
      (ht.trans (hFG q hq).symm)
    exact hh.2
  have hcoord : ContinuousOn (fun q=>fun _ : Fin 1=>2*(G q).val-1) e.target := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuousOn_const.mul (continuous_subtype_val.comp_continuousOn hG)).sub
      continuousOn_const
  apply hcoord.congr
  intro q hq
  funext i
  fin_cases i
  have hh:=edgeIntervalParam_eq_of_closedBall (ball_subset_closedBall (e.map_target hq))
  change (G q).val=((e.symm q) 0+1)/2 at hh
  change (e.symm q) 0=2*(G q).val-1
  linarith only [hh]

theorem boundaryPoint_representative {z : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc} (hz :
  ‖z.val‖=1) :
    ∃r∈Ico (0:ℝ) 1,_root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint r=z := by
  let w : Circle:=⟨z.val,mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨a,ha,hea⟩:=Circle.periodic_exp.exists_mem_Ico Real.two_pi_pos z.val.arg (0:ℝ)
  have hwa : Circle.exp a=w:=hea.symm.trans (Circle.exp_arg w)
  simp only [zero_add] at ha
  refine ⟨a/(2*Real.pi),⟨div_nonneg ha.1 Real.two_pi_pos.le,
    (div_lt_one Real.two_pi_pos).mpr ha.2⟩,?_⟩
  apply Subtype.ext
  change (Circle.exp (2*Real.pi*(a/(2*Real.pi))):ℂ)=z.val
  have hh : 2*Real.pi*(a/(2*Real.pi))=a := by field_simp
  rw [hh]
  exact congrArg Subtype.val hwa

theorem sidePoint_boundary_cover {g : ℕ} (hg : 0<g) {z :
  _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc} (hz : ‖z.val‖=1) :
    ∃(d : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side g)(t : unitInterval),_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint d t=z := by
  obtain ⟨r,hr,rfl⟩:=boundaryPoint_representative hz
  let x : ℝ:=4*(g:ℝ)*r
  have hx : 0≤x:=mul_nonneg (by positivity) hr.1
  have hgpos : (0:ℝ)<g:=Nat.cast_pos.mpr hg
  have hxr : x<4*(g:ℝ) := by dsimp [x];nlinarith only [hr.2,hgpos]
  let n : ℕ:=⌊x⌋₊
  have hn : n<4*g := by
    apply (Nat.floor_lt hx).mpr
    exact_mod_cast hxr
  have hdiv : n/4<g := by omega
  let d : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side g:=(⟨n/4,hdiv⟩,⟨n%4,Nat.mod_lt _ (by norm_num)⟩)
  let t : unitInterval:=⟨x-(n:ℝ),by
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le hx)
    · have hh:=Nat.lt_floor_add_one x
      dsimp [n]
      linarith only [hh]⟩
  refine ⟨d,t,?_⟩
  have hnclock : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sideClock d=n := by
    change 4*(n/4)+n%4=n
    omega
  unfold _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint
  rw [hnclock]
  congr 1
  change ((n:ℝ)+(x-(n:ℝ)))/(4*(g:ℝ))=r
  have hg0 : (g:ℝ)≠0 := (Nat.cast_pos.mpr hg).ne'
  dsimp [x]
  field_simp
  ring

theorem core_side_quotient_ne_vertex {g : ℕ} (d : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Side
  g) (t : unitInterval)
    (ht : 0<t.val ∧ t.val<1) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint d t)≠_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0 := by
  intro he
  have he0:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_endpoint_quotient_zero d 0 (Or.inl rfl)
  rcases quotient_core_side_fiber d t ht (he0.trans he.symm) with h|h
  · have hh:=(_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_core_unique d d t 0 ht
    h.symm).2
    have hv:=congrArg Subtype.val hh
    change t.val=0 at hv
    linarith only [hv,ht.1]
  · have ht' : 0<(unitInterval.symm t).val ∧ (unitInterval.symm t).val<1 := by
      change 0<1-t.val ∧ 1-t.val<1
      constructor <;> linarith only [ht.1,ht.2]
    have hh:=(_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_core_unique
      (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.mate d) d (unitInterval.symm t) 0 ht' h.symm).2
    have hv:=congrArg Subtype.val hh
    change 1-t.val=0 at hv
    linarith only [hv,ht.2]

theorem edgeCell_open_images_disjoint {g : ℕ} (d e : Edge g) (hde : d≠e) :
    Disjoint (edgeCell d '' ball 0 1) (edgeCell e '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro q ⟨v,hv,rfl⟩ ⟨w,_hw,hweq⟩
  have hh:=edge_core_quotient_fiber d e (edgeIntervalParam v) (edgeIntervalParam w)
    (edgeIntervalParam_mem_Ioo hv) hweq
  exact hde hh.1.symm

theorem vertex_edge_open_images_disjoint {g : ℕ} (d : Edge g) :
    Disjoint (vertexCell g '' ball 0 1) (edgeCell d '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro q ⟨v,_hv,rfl⟩ ⟨w,hw,hweq⟩
  exact core_side_quotient_ne_vertex (edgeSide d) (edgeIntervalParam w)
    (edgeIntervalParam_mem_Ioo hw) hweq

theorem top_edge_open_images_disjoint {g : ℕ} (d : Edge g) :
    Disjoint (topCell g '' ball 0 1) (edgeCell d '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro q ⟨v,hv,rfl⟩ ⟨w,_hw,hweq⟩
  have hh:=quotient_interior_fiber_singleton (topCellMap_interior_norm hv) hweq
  have hn:=congrArg (fun z : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc=>‖z.val‖) hh
  rw [sidePoint_norm_one] at hn
  linarith only [hn,topCellMap_interior_norm hv]

theorem top_vertex_open_images_disjoint (g : ℕ) :
    Disjoint (topCell g '' ball 0 1) (vertexCell g '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro q ⟨v,hv,rfl⟩ ⟨w,_hw,hweq⟩
  change Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
    g) (_root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint (0/(4*(g:ℝ))))=
    Quot.mk _ (closedDiscClamp (cubeDiscHomeomorph v)) at hweq
  have hh:=quotient_interior_fiber_singleton (topCellMap_interior_norm hv) hweq
  have hn:=congrArg (fun z : _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc=>‖z.val‖) hh
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint_norm] at hn
  linarith only [hn,topCellMap_interior_norm hv]

theorem edgeCell_closedBall_contains_side {g : ℕ} (d : Edge g) (t : unitInterval) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide d) t)∈edgeCell d '' closedBall 0 1 := by
  let v : Fin 1→ℝ:=fun _=>2*t.val-1
  have hv : v∈closedBall 0 1 := by
    rw [mem_closedBall_zero_iff]
    change ‖fun _ : Fin 1=>2*t.val-1‖≤1
    rw [pi_norm_const,Real.norm_eq_abs,abs_le]
    constructor <;> linarith only [t.property.1,t.property.2]
  have hp : edgeIntervalParam v=t := by
    apply Subtype.ext
    rw [edgeIntervalParam_eq_of_closedBall hv]
    dsimp [v]
    ring
  exact ⟨v,hv,by change Quot.mk _ (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide d) (edgeIntervalParam v))=_;rw [hp]⟩

theorem boundary_quotient_edge_cover {g : ℕ} (hg : 0<g) {z :
  _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.Disc} (hz : ‖z.val‖=1) :
    ∃d : Edge g,Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) z∈edgeCell d '' closedBall 0 1 := by
  obtain ⟨⟨i,j⟩,t,rfl⟩:=sidePoint_boundary_cover hg hz
  fin_cases j
  · exact ⟨(i,0),edgeCell_closedBall_contains_side (i,0) t⟩
  · exact ⟨(i,1),edgeCell_closedBall_contains_side (i,1) t⟩
  · refine ⟨(i,0),?_⟩
    have he:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sideRelated_quotient_eq (g:=g) (z:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide (i,0)) (unitInterval.symm t))
      (w:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint
        (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.mate (edgeSide (i,0))) t)
      ⟨edgeSide (i,0),unitInterval.symm t,rfl,by rw [unitInterval.symm_symm]⟩
    have hh:=edgeCell_closedBall_contains_side (i,0) (unitInterval.symm t)
    rw [he] at hh
    exact hh
  · refine ⟨(i,1),?_⟩
    have he:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sideRelated_quotient_eq (g:=g) (z:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint (edgeSide (i,1)) (unitInterval.symm t))
      (w:=_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint
        (_root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.mate (edgeSide (i,1))) t)
      ⟨edgeSide (i,1),unitInterval.symm t,rfl,by rw [unitInterval.symm_symm]⟩
    have hh:=edgeCell_closedBall_contains_side (i,1) (unitInterval.symm t)
    rw [he] at hh
    exact hh

theorem edgeCell_sphere_vertex {g : ℕ} (d : Edge g) {v : Fin 1→ℝ} (hv : v∈sphere 0 1) :
    edgeCell d v=_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0 := by
  have he : v=fun _ : Fin 1=>v 0 := by funext i;fin_cases i;rfl
  have hn : |v 0|=1 := by
    have hh:=mem_sphere_zero_iff_norm.mp hv
    have hn:=congrArg (fun w : Fin 1→ℝ=>‖w‖) he
    rw [pi_norm_const,Real.norm_eq_abs] at hn
    exact hn.symm.trans hh
  have hcases : v 0=1 ∨ v 0=-1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using hn
  have hp:=edgeIntervalParam_eq_of_closedBall (sphere_subset_closedBall hv)
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.sidePoint_endpoint_quotient_zero
  rcases hcases with h|h
  · right
    apply Subtype.ext
    change (edgeIntervalParam v).val=1
    rw [hp,h]
    norm_num
  · left
    apply Subtype.ext
    change (edgeIntervalParam v).val=0
    rw [hp,h]
    norm_num

theorem topCell_sphere_edge_cover {g : ℕ} (hg : 0<g) {v : Fin 2→ℝ} (hv : v∈sphere 0 1) :
    ∃d : Edge g,topCell g v∈edgeCell d '' closedBall 0 1 := by
  have hc : ‖cubeDiscHomeomorph v‖≤1:=
    (cubeDiscHomeomorph_closedBall_iff v).mpr (sphere_subset_closedBall hv)
  have hn : ‖cubeDiscHomeomorph v‖=1 := by
    apply le_antisymm hc
    by_contra hh
    have hb:=(cubeDiscHomeomorph_openBall_iff v).mp (lt_of_not_ge hh)
    exact (ne_of_lt (mem_ball_zero_iff.mp hb)) (mem_sphere_zero_iff_norm.mp hv)
  apply boundary_quotient_edge_cover hg
  rw [closedDiscClamp_eq_of_norm_le hc]
  exact hn

/-- The actual handle cell decomposition has one vertex, two edges per handle, and one face. -/
abbrev Cell (g : ℕ) : ℕ→Type
  | 0=>PUnit
  | 1=>Edge g
  | 2=>PUnit
  | _+3=>PEmpty

def cellMap (g : ℕ) : (n : ℕ)→Cell g n→PartialEquiv (Fin n→ℝ) (Quot
  (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g))
  | 0,_=>vertexCell g
  | 1,d=>edgeCell d
  | 2,_=>topCell g
  | _+3,i=>nomatch i

theorem cell_dimension_le (g n : ℕ) (i : Cell g n) : n≤2 := by
  cases n with
  | zero=>omega
  | succ n=>
    cases n with
    | zero=>omega
    | succ n=>
      cases n with
      | zero=>omega
      | succ n=>exact i.elim

theorem cell_finite (g n : ℕ) : Finite (Cell g n) := by
  cases n with
  | zero=>infer_instance
  | succ n=>
    cases n with
    | zero=>infer_instance
    | succ n=>
      cases n <;> infer_instance

theorem cell_eventually_empty (g : ℕ) : ∀ᶠ n in atTop,IsEmpty (Cell g n) := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact ⟨fun i=>by have hh:=cell_dimension_le g n i;omega⟩

theorem cellMap_source (g n : ℕ) (i : Cell g n) : (cellMap g n i).source=ball 0 1 := by
  have hn:=cell_dimension_le g n i
  interval_cases n <;> rfl

theorem cellMap_continuousOn (g n : ℕ) (i : Cell g n) :
    ContinuousOn (cellMap g n i) (closedBall 0 1) := by
  have hn:=cell_dimension_le g n i
  interval_cases n
  · exact vertexCell_continuousOn g
  · exact edgeCell_continuousOn i
  · exact topCell_continuousOn g

theorem cellMap_symm_continuousOn (g n : ℕ) (i : Cell g n) :
    ContinuousOn (cellMap g n i).symm (cellMap g n i).target := by
  have hn:=cell_dimension_le g n i
  interval_cases n
  · exact vertexCell_symm_continuousOn g
  · exact edgeCell_symm_continuousOn i
  · exact topCell_symm_continuousOn g

theorem cellMap_pairwiseDisjoint (g : ℕ) :
    (univ : Set (Σn,Cell g n)).PairwiseDisjoint
      (fun ni=>cellMap g ni.1 ni.2 '' ball 0 1) := by
  rintro ⟨n,i⟩ _ ⟨m,j⟩ _ hne
  have hn:=cell_dimension_le g n i
  have hm:=cell_dimension_le g m j
  interval_cases n <;> interval_cases m
  · have hij : i=j:=Subsingleton.elim _ _
    subst j
    exact (hne rfl).elim
  · exact vertex_edge_open_images_disjoint j
  · exact (top_vertex_open_images_disjoint g).symm
  · exact (vertex_edge_open_images_disjoint i).symm
  · apply edgeCell_open_images_disjoint i j
    intro hij
    subst j
    exact hne rfl
  · exact (top_edge_open_images_disjoint i).symm
  · exact top_vertex_open_images_disjoint g
  · exact top_edge_open_images_disjoint j
  · have hij : i=j:=Subsingleton.elim _ _
    subst j
    exact (hne rfl).elim

theorem vertex_mem_lower_cells (g n : ℕ) (hn : 0<n) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0∈⋃(m<n)(j : Cell g m),cellMap g m j '' closedBall 0 1 := by
  refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨hn,mem_iUnion.mpr ⟨PUnit.unit,?_⟩⟩⟩
  exact ⟨0,by simp,rfl⟩

theorem cellMap_mapsTo (g : ℕ) (hg : 0<g) (n : ℕ) (i : Cell g n) :
    MapsTo (cellMap g n i) (sphere 0 1)
      (⋃(m<n)(j : Cell g m),cellMap g m j '' closedBall 0 1) := by
  have hn:=cell_dimension_le g n i
  interval_cases n
  · intro v hv
    have he : v=0:=Subsingleton.elim _ _
    have hh:=mem_sphere_zero_iff_norm.mp hv
    rw [he,norm_zero] at hh
    norm_num at hh
  · intro v hv
    change edgeCell i v∈_
    rw [edgeCell_sphere_vertex i hv]
    exact vertex_mem_lower_cells g 1 (by omega)
  · intro v hv
    obtain ⟨d,hd⟩:=topCell_sphere_edge_cover hg hv
    exact mem_iUnion.mpr ⟨1,mem_iUnion.mpr ⟨by omega,mem_iUnion.mpr ⟨d,hd⟩⟩⟩

theorem cellMap_closedBall_union (g : ℕ) :
    ⋃(n : ℕ)(j : Cell g n),cellMap g n j '' closedBall 0 1=univ := by
  apply eq_univ_of_forall
  intro q
  refine mem_iUnion.mpr ⟨2,mem_iUnion.mpr ⟨PUnit.unit,?_⟩⟩
  change q∈topCell g '' closedBall 0 1
  rw [topCell_closedBall_image]
  trivial

/-- A genuine finite CW structure on the original positive-genus disc edge quotient. -/
@[instance_reducible] def canonicalHandleCW (g : ℕ) (hg : 0<g) :
    Topology.CWComplex (univ : Set (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g))) :=
  Topology.CWComplex.mkFinite univ (Cell g) (cellMap g) (cell_eventually_empty g)
    (cell_finite g) (cellMap_source g) (cellMap_continuousOn g)
    (cellMap_symm_continuousOn g) (cellMap_pairwiseDisjoint g)
    (cellMap_mapsTo g hg) (cellMap_closedBall_union g)

theorem canonicalHandleCW_finite (g : ℕ) (hg : 0<g) :
    letI:=canonicalHandleCW g hg
    Topology.RelCWComplex.Finite (univ : Set (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
      g))) :=
  Topology.CWComplex.finite_mkFinite univ (Cell g) (cellMap g) (cell_eventually_empty g)
    (cell_finite g) (cellMap_source g) (cellMap_continuousOn g)
    (cellMap_symm_continuousOn g) (cellMap_pairwiseDisjoint g)
    (cellMap_mapsTo g hg) (cellMap_closedBall_union g)

theorem canonicalHandleCW_card_zero (g : ℕ) (hg : 0<g) :
    letI:=canonicalHandleCW g hg
    Nat.card (Topology.RelCWComplex.cell (univ : Set (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g))) 0)=1 := by
  change Nat.card (Cell g 0)=1
  simp [Cell]

theorem canonicalHandleCW_card_one (g : ℕ) (hg : 0<g) :
    letI:=canonicalHandleCW g hg
    Nat.card (Topology.RelCWComplex.cell (univ : Set (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g))) 1)=2*g := by
  change Nat.card (Fin g×Fin 2)=2*g
  simp [mul_comm]

theorem canonicalHandleCW_card_two (g : ℕ) (hg : 0<g) :
    letI:=canonicalHandleCW g hg
    Nat.card (Topology.RelCWComplex.cell (univ : Set (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g))) 2)=1 := by
  change Nat.card (Cell g 2)=1
  simp [Cell]

theorem canonicalHandleCW_card_of_three_le (g : ℕ) (hg : 0<g) (n : ℕ) (hn : 3≤n) :
    letI:=canonicalHandleCW g hg
    Nat.card (Topology.RelCWComplex.cell (univ : Set (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g))) n)=0 := by
  change Nat.card (Cell g n)=0
  have : IsEmpty (Cell g n):=⟨fun i=>by have hh:=cell_dimension_le g n i;omega⟩
  exact Nat.card_of_isEmpty

end LowDimensionalTopology.Geometry.Surfaces.HandleCW
