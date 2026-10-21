/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletCycleLowerBounds
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAngles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAccidentalCycles
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletCycleRadius
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DiscCircleDistance
public import Mathlib.Data.Fintype.Sort
@[expose] public section
noncomputable section
open Set
open scoped Complex.UnitDisc BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Finite points on a genuine Euclidean norm circle have a constructed strictly
increasing argument enumeration; no circular ordering data are assumed. -/
theorem finite_circle_argument_order (s : Finset Complex.UnitDisc)
    (hs : ∀x∈s,∀y∈s,‖(x:ℂ)‖=‖(y:ℂ)‖) :
    ∃e : Fin s.card≃s,StrictMono (fun i=>Complex.arg ((e i).val:ℂ)) := by
  classical
  let f : s→ℝ:=fun x=>Complex.arg (x.val:ℂ)
  have hi : Function.Injective f:=by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact Complex.ext_norm_arg (hs x.val x.property y.val y.property) hxy
  let circleArgumentLinearOrder : LinearOrder s:=LinearOrder.lift' f hi
  let e : Fin s.card≃o s:=monoEquivOfFin s (Fintype.card_coe s)
  refine ⟨e.toEquiv,?_⟩
  intro i j hij
  exact e.strictMono hij

/-- The genuine forward argument gap, including its single wrap through the
chosen principal-argument cut. -/
def cyclicArgumentGap {n : ℕ} (a : Fin (n+1)→ℝ) (i : Fin (n+1)) : ℝ:=
  a (finRotate (n+1) i)-a i+if i=Fin.last n then 2*Real.pi else 0

theorem cyclicArgumentGap_sum {n : ℕ} (a : Fin (n+1)→ℝ) :
    ∑i,cyclicArgumentGap a i=2*Real.pi := by
  classical
  simp only [cyclicArgumentGap,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have he : ∑i,a (finRotate (n+1) i)=∑i,a i:=Equiv.sum_comp (finRotate (n+1)) a
  rw [he,sub_self,zero_add]
  simp

theorem cyclicArgumentGap_positive {n : ℕ} (a : Fin (n+1)→ℝ) (ha : StrictMono a)
    (hb : ∀i,a i∈Ioc (-Real.pi) Real.pi) (i : Fin (n+1)) :
    0<cyclicArgumentGap a i := by
  classical
  by_cases hi : i=Fin.last n
  · subst i
    simp only [cyclicArgumentGap,finRotate_last,ite_true]
    linarith [(hb 0).1,(hb (Fin.last n)).2]
  · have hr:=coe_finRotate_of_ne_last hi
    have hh : i<finRotate (n+1) i:=by change i.val<(finRotate (n+1) i).val;omega
    have ht:=ha hh
    simp only [cyclicArgumentGap,hi,ite_false,add_zero]
    exact sub_pos.mpr ht

/-- The actual half-arcs supplied by the constructed circular enumeration
have exactly the source total-angle budget. -/
theorem cyclicArgumentHalfGap_sum {n : ℕ} (a : Fin (n+1)→ℝ) :
    ∑i,cyclicArgumentGap a i/2=Real.pi := by
  rw [←Finset.sum_div,cyclicArgumentGap_sum]
  ring

/-- Normalize the actual original disc center, using a genuine isometry. -/
def cycleOriginCoordinate {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) : P.domain.carrier≃ₜComplex.UnitDisc:=
  P.finiteCoordinate.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate
    w))

theorem cycleOriginCoordinate_norm {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (w x : P.domain.carrier) (r : ℝ) (hx : P.hyperbolicDist w x=r) :
    ‖(cycleOriginCoordinate P w x:ℂ)‖=Real.tanh (r/2) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_distance_zero_eq_iff _ r).mp
  let cycleOrderDiscMetric : MetricSpace Complex.UnitDisc:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have hi:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry (P.finiteCoordinate
    w)).dist_eq
    (P.finiteCoordinate w) (P.finiteCoordinate x)
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] at hi
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self] at hi
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate w) (P.finiteCoordinate x))=r
  rw [hi,←P.hyperbolicDist_eq_discPathDist]
  exact hx

/-- Sorting actual original circle points by a constructed principal argument
keeps their original geometric identities and supplies all circular-order data. -/
theorem finite_original_circle_argument_order {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (s : Finset P.domain.carrier)
    (r : ℝ) (hs : ∀x∈s,P.hyperbolicDist w x=r) :
    ∃e : Fin s.card≃s,StrictMono (fun i=>Complex.arg (cycleOriginCoordinate P w (e i).val:ℂ)) := by
  classical
  let C:=cycleOriginCoordinate P w
  let t:=s.image C
  have ht : ∀x∈t,∀y∈t,‖(x:ℂ)‖=‖(y:ℂ)‖:=by
    rintro x hx y hy
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hy
    exact (cycleOriginCoordinate_norm P w a r (hs a ha)).trans
      (cycleOriginCoordinate_norm P w b r (hs b hb)).symm
  obtain ⟨e,he⟩:=finite_circle_argument_order t ht
  have hc : t.card=s.card:=Finset.card_image_of_injective s C.injective
  let e' : Fin s.card≃t:=(finCongr hc).symm.trans e
  let eC : s≃t:=C.toEquiv.imageFinset s
  refine ⟨e'.trans eC.symm,?_⟩
  intro i j hij
  have hij' : ((finCongr hc).symm i)<((finCongr hc).symm j):=hij
  have hh:=he hij'
  change Complex.arg (C ((e'.trans eC.symm) i).val:ℂ)<
    Complex.arg (C ((e'.trans eC.symm) j).val:ℂ)
  have hCi (k : Fin s.card) : C ((e'.trans eC.symm) k).val=(e' k).val:=
    congrArg Subtype.val (eC.apply_symm_apply (e' k))
  rw [hCi i,hCi j]
  exact hh

/-- Every literal actual Dirichlet vertex cycle has an original-point
argument enumeration, without prescribing its points or their angular order. -/
theorem dirichlet_cycle_argument_order {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    ∃s : Finset P.domain.carrier,
      (↑s:Set P.domain.carrier)=fuchsianPolygonCycle P (dirichletDomain P w) x ∧
      ∃e : Fin s.card≃s,
        StrictMono (fun i=>Complex.arg (cycleOriginCoordinate P w (e i).val:ℂ)) := by
  classical
  have hP:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let s:=(hP.locallyFinite.cycle_finite x).toFinset
  have hs : (↑s:Set P.domain.carrier)=fuchsianPolygonCycle P (dirichletDomain P w) x:=
    (hP.locallyFinite.cycle_finite x).coe_toFinset
  refine ⟨s,hs,finite_original_circle_argument_order P w s (P.hyperbolicDist w x) ?_⟩
  intro y hy
  have hxc : x∈fuchsianPolygonCycle P (dirichletDomain P w) x:=
    ⟨(hx.mem_frontier hP.locallyFinite.fundamental).1,⟨1,one_smul _ _⟩⟩
  have hyc : y∈fuchsianPolygonCycle P (dirichletDomain P w) x:=by rw [←hs];exact hy
  have he:=dirichlet_cycle_distance_to_center_eq P w x hyc hxc
  rw [P.hyperbolicDist_comm w y,P.hyperbolicDist_comm w x]
  exact he

/-- Principal-argument half-gaps for a finite original point list, with the
unique full-turn correction selected by its actual final index. -/
def circleHalfArc {n : ℕ} (a : Fin n→ℝ) (i : Fin n) : ℝ:=
  (a (finRotate n i)-a i+if i.val+1=n then 2*Real.pi else 0)/2

theorem circleHalfArc_positive {n : ℕ} (a : Fin n→ℝ) (ha : StrictMono a)
    (hb : ∀i,a i∈Ioc (-Real.pi) Real.pi) (i : Fin n) : 0<circleHalfArc a i := by
  cases n with
  | zero=>exact Fin.elim0 i
  | succ n=>
    have hi : (i.val+1=n+1)↔i=Fin.last n:=by
      constructor
      · intro hh;apply Fin.ext;change i.val=n;omega
      · intro hh;subst i;rfl
    have he : circleHalfArc a i=cyclicArgumentGap a i/2:=by
      simp only [circleHalfArc,cyclicArgumentGap,hi]
    rw [he]
    exact div_pos (cyclicArgumentGap_positive a ha hb i) (by norm_num)

theorem circleHalfArc_sum {n : ℕ} (hn : 0<n) (a : Fin n→ℝ) :
    ∑i,circleHalfArc a i=Real.pi := by
  cases n with
  | zero=>omega
  | succ n=>
    have he (i : Fin (n+1)) : circleHalfArc a i=cyclicArgumentGap a i/2:=by
      have hi : (i.val+1=n+1)↔i=Fin.last n:=by
        constructor
        · intro hh;apply Fin.ext;change i.val=n;omega
        · intro hh;subst i;rfl
      simp only [circleHalfArc,cyclicArgumentGap,hi]
    simp only [he]
    exact cyclicArgumentHalfGap_sum a

/-- The original actual accidental Dirichlet cycle supplies a genuine ordered
point list, positive half-arcs and the exact total pi; none are extra premises. -/
theorem dirichlet_cycle_half_arc_data {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (ha : IsAccidentalFuchsianPoint P x) :
    ∃(n : ℕ) (_hn : 3≤n) (p : Fin n→P.domain.carrier),
      Function.Injective p ∧ Set.range p=fuchsianPolygonCycle P (dirichletDomain P w) x ∧
      StrictMono (fun i=>Complex.arg (cycleOriginCoordinate P w (p i):ℂ)) ∧
      (∀i,0<circleHalfArc (fun j=>Complex.arg (cycleOriginCoordinate P w (p j):ℂ)) i) ∧
      (∑i,circleHalfArc (fun j=>Complex.arg (cycleOriginCoordinate P w (p j):ℂ)) i)=Real.pi := by
  classical
  obtain ⟨s,hs,e,he⟩:=dirichlet_cycle_argument_order P w hw x hx
  have hP:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have hc:=hP.accidental_vertex_cycle_length_ge_three x hx ha
  have hn : 3≤s.card:=by
    unfold fuchsianPolygonCycleLength at hc
    rw [←hs] at hc
    simpa only [Set.ncard_coe_finset] using hc
  let p : Fin s.card→P.domain.carrier:=fun i=>(e i).val
  have hp : Function.Injective p:=fun i j hij=>e.injective (Subtype.ext hij)
  have hpr : Set.range p=fuchsianPolygonCycle P (dirichletDomain P w) x:=by
    rw [←hs]
    ext y
    constructor
    · rintro ⟨i,rfl⟩;exact (e i).property
    · intro hy;exact ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)⟩
  refine ⟨s.card,hn,p,hp,hpr,he,?_,circleHalfArc_sum (by omega) _⟩
  intro i
  exact circleHalfArc_positive _ he (fun j=>Complex.arg_mem_Ioc _) i

/-- The two base angles of an actual isosceles hyperbolic triangle agree. -/
theorem cycle_isosceles_base_angles (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (he :
  T.lengthB=T.lengthC) :
    T.beta=T.gamma := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.angle_eq_of_hyperbolic_cosine_rule T.lengths_pos.2.2 T.lengths_pos.1
    ⟨T.angles_mem_Ioo.2.1.1.le,T.angles_mem_Ioo.2.1.2.le⟩
    ⟨T.angles_mem_Ioo.2.2.1.le,T.angles_mem_Ioo.2.2.2.le⟩ T.cosine_rule_B
  simpa only [he,mul_comm] using T.cosine_rule_I

/-- The exact source half-apex identity follows directly from the two cosine
rules of the genuine isosceles triangle, without an assumed altitude. -/
theorem cycle_isosceles_half_apex_identity (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (he :
  T.lengthB=T.lengthC) :
    Real.cosh T.lengthC*Real.tan (T.alpha/2)*Real.tan T.beta=1 := by
  have hbg:=cycle_isosceles_base_angles T he
  have hsum:=T.angle_sum_lt_pi
  rw [←hbg] at hsum
  have hα : T.alpha/2∈Ioo (0:ℝ) (Real.pi/2):=
    ⟨by linarith [T.angles_mem_Ioo.1.1],by linarith [T.angles_mem_Ioo.1.2]⟩
  have hβ : T.beta∈Ioo (0:ℝ) (Real.pi/2):=
    ⟨T.angles_mem_Ioo.2.1.1,by linarith [T.angles_mem_Ioo.1.1]⟩
  have hcα : Real.cos (T.alpha/2)≠0:=ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hα.1,Real.pi_pos],hα.2⟩)
  have hcβ : Real.cos T.beta≠0:=ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hβ.1,Real.pi_pos],hβ.2⟩)
  have hsα : Real.sin T.alpha≠0:=ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2)
  have hsβ : Real.sin T.beta≠0:=ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    T.angles_mem_Ioo.2.1.1 T.angles_mem_Ioo.2.1.2)
  have hid:=(eq_div_iff (mul_ne_zero hsα hsβ)).mp T.cosine_rule_II
  rw [←hbg] at hid
  have hs : Real.sin T.alpha=2*Real.sin (T.alpha/2)*Real.cos (T.alpha/2):=by
    have hh : 2*(T.alpha/2)=T.alpha:=by ring
    simpa only [hh] using Real.sin_two_mul (T.alpha/2)
  have hc : Real.cos T.alpha=2*(Real.cos (T.alpha/2))^2-1:=by
    have hh : 2*(T.alpha/2)=T.alpha:=by ring
    simpa only [hh] using Real.cos_two_mul (T.alpha/2)
  rw [hs,hc] at hid
  rw [Real.tan_eq_sin_div_cos,Real.tan_eq_sin_div_cos]
  field_simp
  apply mul_left_cancel₀ hcα
  nlinarith only [hid]

end LowDimensionalTopology.Geometry.Fuchsian
