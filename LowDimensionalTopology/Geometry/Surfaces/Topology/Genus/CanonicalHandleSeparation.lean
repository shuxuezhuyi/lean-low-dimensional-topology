/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleWindings
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CompactClosedQuotients
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Surfaces.HandleSeparation

abbrev Disc := Metric.closedBall (0 : ℂ) 1
abbrev Side (g : ℕ) := Fin g×Fin 4

def sideClock {g : ℕ} (d : Side g) : ℕ := 4*d.1.val+d.2.val

def sidePoint {g : ℕ} (d : Side g) (t : unitInterval) : Disc :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint ((((sideClock d : ℕ) : ℝ)+t.val)/(4*(g : ℝ)))

def mate {g : ℕ} (d : Side g) : Side g := (d.1,d.2+2)

theorem mate_involutive {g : ℕ} (d : Side g) : mate (mate d)=d := by
  rcases d with ⟨i,j⟩
  simp only [mate]
  congr 1
  fin_cases j <;> norm_num

theorem clock_bound {g : ℕ} (d : Side g) : sideClock d+1≤4*g := by
  have hi := d.1.isLt
  have hj := d.2.isLt
  dsimp [sideClock]
  omega

theorem boundaryPoint_clock_period {g : ℕ} (hg : 0<g) {x y : ℝ}
    (heq : _root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint
      (x/(4*g))=_root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint (y/(4*g))) :
    ∃m : ℤ,x=y+(m : ℝ)*(4*g) := by
  have hN : (4 : ℝ)*g≠0 := by positivity
  have hpi : 2*Real.pi≠0 := by positivity
  have he : Circle.exp (2*Real.pi*(x/(4*g)))=Circle.exp (2*Real.pi*(y/(4*g))) := by
    apply Subtype.ext
    exact congrArg (fun z : Disc => (z : ℂ)) heq
  obtain ⟨m,hm⟩ := Circle.exp_eq_exp.mp he
  refine ⟨m,?_⟩
  have hh : (2*Real.pi)*(x/(4*g))=(2*Real.pi)*(y/(4*g)+(m : ℝ)) := by linear_combination hm
  have hd := mul_left_cancel₀ hpi hh
  field_simp [hN] at hd
  linarith only [hd]

theorem boundaryPoint_clock_injective {g : ℕ} (hg : 0<g) {x y : ℝ}
    (hx : x∈Ioo (0 : ℝ) (4*(g : ℝ))) (hy : y∈Icc (0 : ℝ) (4*(g : ℝ)))
    (heq : _root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint (x/(4*g))=_root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint (y/(4*g))) : x=y := by
  obtain ⟨m,hm⟩ := boundaryPoint_clock_period hg heq
  have hN : 0<(4 : ℝ)*g := by positivity
  have hm0 : m=0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg|hpos
    · have hi : m≤-1 := by omega
      have hr : (m : ℝ)≤-1 := by exact_mod_cast hi
      have hh := mul_le_mul_of_nonneg_right hr hN.le
      linarith only [hm,hx.1,hy.2,hh]
    · have hi : 1≤m := by omega
      have hr : 1≤(m : ℝ) := by exact_mod_cast hi
      have hh := mul_le_mul_of_nonneg_right hr hN.le
      linarith only [hm,hx.2,hy.1,hh]
  simpa only [hm0,Int.cast_zero,zero_mul,add_zero] using hm

theorem sidePoint_core_unique {g : ℕ} (d e : Side g) (t u : unitInterval)
    (ht : 0<t.val ∧ t.val<1) (heq : sidePoint d t=sidePoint e u) : d=e ∧ t=u := by
  have hg : 0<g := by have h := d.1.isLt;omega
  have hd := clock_bound d
  have he := clock_bound e
  have hdR : (sideClock d : ℝ)+1≤4*(g : ℝ) := by exact_mod_cast hd
  have heR : (sideClock e : ℝ)+1≤4*(g : ℝ) := by exact_mod_cast he
  have hd0 : (0 : ℝ)≤(sideClock d : ℝ) := by positivity
  have he0 : (0 : ℝ)≤(sideClock e : ℝ) := by positivity
  have hc : (sideClock d : ℝ)+t.val=(sideClock e : ℝ)+u.val := by
    apply boundaryPoint_clock_injective hg
    · exact ⟨by linarith only [hd0,ht.1],by linarith only [hdR,ht.2]⟩
    · exact ⟨by linarith only [he0,u.property.1],by linarith only [heR,u.property.2]⟩
    · exact heq
  have hclock : sideClock d=sideClock e := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt|hgt
    · have hnat : sideClock d+1≤ sideClock e := by omega
      have hr : (sideClock d : ℝ)+1≤(sideClock e : ℝ) := by exact_mod_cast hnat
      linarith only [hc,hr,ht.2,u.property.1]
    · have hnat : sideClock e+1≤ sideClock d := by omega
      have hr : (sideClock e : ℝ)+1≤(sideClock d : ℝ) := by exact_mod_cast hnat
      linarith only [hc,hr,ht.1,u.property.2]
  have hde : d=e := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [sideClock] at hclock
    · have hj := d.2.isLt;have hk := e.2.isLt;omega
    · have hj := d.2.isLt;have hk := e.2.isLt;omega
  refine ⟨hde,Subtype.ext ?_⟩
  rw [hclock] at hc
  linarith only [hc]

def vertices (g : ℕ) : Set Disc :=
  Set.range (fun d : Side g => sidePoint d 0) ∪ Set.range (fun d : Side g => sidePoint d 1)

theorem vertices_finite (g : ℕ) : (vertices g).Finite :=
  (finite_range _).union (finite_range _)

theorem sidePoint_vertex_iff {g : ℕ} (d : Side g) (t : unitInterval) :
    sidePoint d t∈vertices g ↔ t=0∨t=1 := by
  constructor
  · intro hv
    by_cases ht0 : t=0
    · exact Or.inl ht0
    by_cases ht1 : t=1
    · exact Or.inr ht1
    have ht0' : t.val≠0 := fun h => ht0 (Subtype.ext h)
    have ht1' : t.val≠1 := fun h => ht1 (Subtype.ext h)
    have ht : 0<t.val ∧ t.val<1 :=
      ⟨lt_of_le_of_ne t.property.1 ht0'.symm,lt_of_le_of_ne t.property.2 ht1'⟩
    rcases hv with ⟨e,he⟩|⟨e,he⟩
    · exact False.elim (ht0 (sidePoint_core_unique d e t 0 ht he.symm).2)
    · exact False.elim (ht1 (sidePoint_core_unique d e t 1 ht he.symm).2)
  · rintro (rfl|rfl)
    · exact Or.inl (mem_range_self d)
    · exact Or.inr (mem_range_self d)

theorem sidePoint_core_of_not_vertex {g : ℕ} (d : Side g) (t : unitInterval)
    (ht : sidePoint d t∉vertices g) : 0<t.val ∧ t.val<1 := by
  have hne := not_or.mp (fun h => ht ((sidePoint_vertex_iff d t).mpr h))
  exact ⟨lt_of_le_of_ne t.property.1 (fun h => hne.1 (Subtype.ext h.symm)),
    lt_of_le_of_ne t.property.2 (fun h => hne.2 (Subtype.ext h))⟩

def sideRelated (g : ℕ) (z w : Disc) : Prop :=
  ∃(d : Side g)(t : unitInterval),z=sidePoint d t ∧ w=sidePoint (mate d) (unitInterval.symm t)

theorem sideRelated_symm {g : ℕ} {z w : Disc} (h : sideRelated g z w) : sideRelated g w z := by
  obtain ⟨d,t,rfl,rfl⟩ := h
  refine ⟨mate d,unitInterval.symm t,rfl,?_⟩
  rw [mate_involutive,unitInterval.symm_symm]

theorem sideRelated_vertex_iff {g : ℕ} {z w : Disc} (h : sideRelated g z w) :
    z∈vertices g ↔ w∈vertices g := by
  obtain ⟨d,t,rfl,rfl⟩ := h
  rw [sidePoint_vertex_iff,sidePoint_vertex_iff]
  constructor
  · rintro (rfl|rfl) <;> simp
  · rintro (h|h)
    · exact Or.inr (by simpa only [unitInterval.symm_symm,unitInterval.symm_zero] using congrArg unitInterval.symm h)
    · exact Or.inl (by simpa only [unitInterval.symm_symm,unitInterval.symm_one] using congrArg unitInterval.symm h)

theorem sideRelated_comp_of_not_vertex {g : ℕ} {x y z : Disc}
    (hxy : sideRelated g x y) (hyz : sideRelated g y z) (hy : y∉vertices g) : x=z := by
  obtain ⟨d,t,rfl,rfl⟩ := hxy
  obtain ⟨e,u,he,rfl⟩ := hyz
  have hcore := sidePoint_core_of_not_vertex (mate d) (unitInterval.symm t) hy
  obtain ⟨hde,htu⟩ := sidePoint_core_unique (mate d) e (unitInterval.symm t) u hcore he
  rw [←hde,←htu,mate_involutive,unitInterval.symm_symm]

def closedRelation (g : ℕ) (z w : Disc) : Prop :=
  z=w ∨ sideRelated g z w ∨ (z∈vertices g ∧ w∈vertices g)

theorem closedRelation_refl (g : ℕ) (z : Disc) : closedRelation g z z := Or.inl rfl

theorem closedRelation_symm {g : ℕ} {z w : Disc} (h : closedRelation g z w) : closedRelation g w z := by
  rcases h with h|h|h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl (sideRelated_symm h))
  · exact Or.inr (Or.inr ⟨h.2,h.1⟩)

theorem closedRelation_trans {g : ℕ} {x y z : Disc}
    (hxy : closedRelation g x y) (hyz : closedRelation g y z) : closedRelation g x z := by
  rcases hxy with hxy|hxy|hxy
  · exact hxy.symm ▸ hyz
  · rcases hyz with hyz|hyz|hyz
    · exact hyz ▸ Or.inr (Or.inl hxy)
    · by_cases hy : y∈vertices g
      · exact Or.inr (Or.inr ⟨(sideRelated_vertex_iff hxy).mpr hy,(sideRelated_vertex_iff hyz).mp hy⟩)
      · exact Or.inl (sideRelated_comp_of_not_vertex hxy hyz hy)
    · exact Or.inr (Or.inr ⟨(sideRelated_vertex_iff hxy).mpr hyz.1,hyz.2⟩)
  · rcases hyz with hyz|hyz|hyz
    · exact Or.inr (Or.inr ⟨hxy.1,hyz ▸ hxy.2⟩)
    · exact Or.inr (Or.inr ⟨hxy.1,(sideRelated_vertex_iff hyz).mp hxy.2⟩)
    · exact Or.inr (Or.inr ⟨hxy.1,hyz.2⟩)

theorem sidePoint_continuous {g : ℕ} (d : Side g) : Continuous (sidePoint d) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.handleBoundaryPoint_continuous.comp
    ((continuous_const.add continuous_subtype_val).div_const _)

theorem sideRelated_isClosed (g : ℕ) : IsClosed {p : Disc×Disc | sideRelated g p.1 p.2} := by
  have he : {p : Disc×Disc | sideRelated g p.1 p.2}=
      ⋃d : Side g,Set.range (fun t : unitInterval => (sidePoint d t,sidePoint (mate d) (unitInterval.symm t))) := by
    ext ⟨z,w⟩
    constructor
    · rintro ⟨d,t,rfl,rfl⟩
      exact mem_iUnion.mpr ⟨d,mem_range_self t⟩
    · intro hp
      obtain ⟨d,hd⟩ := mem_iUnion.mp hp
      obtain ⟨t,h⟩ := hd
      exact ⟨d,t,congrArg Prod.fst h.symm,congrArg Prod.snd h.symm⟩
  rw [he]
  apply isClosed_iUnion_of_finite
  intro d
  exact (isCompact_range ((sidePoint_continuous d).prodMk
    ((sidePoint_continuous (mate d)).comp unitInterval.continuous_symm))).isClosed

theorem closedRelation_isClosed (g : ℕ) : IsClosed {p : Disc×Disc | closedRelation g p.1 p.2} :=
  isClosed_diagonal.union ((sideRelated_isClosed g).union
    ((vertices_finite g).isClosed.prod (vertices_finite g).isClosed))

theorem sidePoint_quotient_formula {g : ℕ} (d : Side g) (t : unitInterval) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) (sidePoint d t)=
      _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g (4*(d.1.val : ℝ)+(d.2.val : ℝ)+t.val) := by
  unfold sidePoint sideClock _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex
  push_cast
  rfl

theorem sideRelated_quotient_eq {g : ℕ} {z w : Disc} (h : sideRelated g z w) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) z=Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) w := by
  obtain ⟨⟨i,j⟩,t,rfl,rfl⟩ := h
  rw [sidePoint_quotient_formula,sidePoint_quotient_formula]
  fin_cases j
  · have he : 4*(i.val : ℝ)+2+(1-t.val)=4*i.val+3-t.val := by ring
    simpa [mate,he] using _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex_a g i t
  · have he : 4*(i.val : ℝ)+3+(1-t.val)=4*i.val+4-t.val := by ring
    simpa [mate,he] using _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex_b g i t
  · convert (_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex_a g i (unitInterval.symm t)).symm using 1 <;>
      congr 1 <;> dsimp [mate,unitInterval.symm] <;> ring
  · convert (_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex_b g i (unitInterval.symm t)).symm using 1 <;>
      congr 1 <;> dsimp [mate,unitInterval.symm] <;> ring

theorem blockStart_quotient_zero (g : ℕ) : ∀i : ℕ,i≤g →
    _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g (4*(i : ℝ))=_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0 := by
  intro i
  induction i with
  | zero => intro _;simp
  | succ i ih =>
    intro hi
    have hig : i<g := by omega
    have hb := (_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex_block g ⟨i,hig⟩).2.2
    have hh := hb.trans (ih (by omega))
    convert hh using 1
    congr 1
    push_cast
    ring

theorem blockVertex_quotient_zero {g : ℕ} (i : Fin g) (j : Fin 5) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g (4*(i.val : ℝ)+(j.val : ℝ))=_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0 := by
  have hstart := blockStart_quotient_zero g i.val i.isLt.le
  have hb := _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex_block g i
  fin_cases j
  · simpa only [Fin.val_zero,Nat.cast_zero,add_zero] using hstart
  · simpa using hb.1.trans hstart
  · simpa using hb.2.1.trans hstart
  · have hh := _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex_a g i 0
    have hh' : _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g (4*(i.val : ℝ)+3)=_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g (4*(i.val : ℝ)) := by simpa using hh.symm
    simpa using hh'.trans hstart
  · simpa using hb.2.2.trans hstart

theorem sidePoint_endpoint_quotient_zero {g : ℕ} (d : Side g) (t : unitInterval)
    (ht : t=0∨t=1) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) (sidePoint d t)=_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0 := by
  rw [sidePoint_quotient_formula]
  rcases ht with rfl|rfl
  · simpa only [Icc.coe_zero,add_zero] using blockVertex_quotient_zero d.1 ⟨d.2.val,by have h:=d.2.isLt;omega⟩
  · have hh := blockVertex_quotient_zero d.1 ⟨d.2.val+1,by have h:=d.2.isLt;omega⟩
    simpa only [Icc.coe_one,Nat.cast_add,Nat.cast_one,add_assoc] using hh

theorem vertex_quotient_zero {g : ℕ} {z : Disc} (hz : z∈vertices g) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) z=_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex g 0 := by
  rcases hz with ⟨d,rfl⟩|⟨d,rfl⟩
  · exact sidePoint_endpoint_quotient_zero d 0 (Or.inl rfl)
  · exact sidePoint_endpoint_quotient_zero d 1 (Or.inr rfl)

theorem closedRelation_quotient_eq {g : ℕ} {z w : Disc} (h : closedRelation g z w) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) z=Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) w := by
  rcases h with h|h|h
  · exact congrArg (Quot.mk _) h
  · exact sideRelated_quotient_eq h
  · exact (vertex_quotient_zero h.1).trans (vertex_quotient_zero h.2).symm

theorem generator_closedRelation {g : ℕ} {z w : Disc} (h :
  _root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g z w) :
    closedRelation g z w := by
  cases h with
  | a t i =>
    apply Or.inr ∘ Or.inl
    refine ⟨(i,0),t,?_,?_⟩
    · simp [sidePoint,sideClock]
    · simp [sidePoint,sideClock,mate,unitInterval.symm]
      congr 1
      ring
  | b t i =>
    apply Or.inr ∘ Or.inl
    refine ⟨(i,1),t,?_,?_⟩
    · simp [sidePoint,sideClock]
    · simp [sidePoint,sideClock,mate,unitInterval.symm]
      congr 1
      ring

theorem eqvGen_closedRelation {g : ℕ} {z w : Disc}
    (h : Relation.EqvGen (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) z w) : closedRelation g z w := by
  induction h with
  | rel z w h => exact generator_closedRelation h
  | refl z => exact closedRelation_refl g z
  | symm z w h ih => exact closedRelation_symm ih
  | trans z w u h1 h2 ih1 ih2 => exact closedRelation_trans ih1 ih2

theorem quotient_eq_iff_closedRelation (g : ℕ) (z w : Disc) :
    Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
      g) z=Quot.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) w ↔ closedRelation g z w :=
  ⟨fun h => eqvGen_closedRelation (Quot.eqvGen_exact h),closedRelation_quotient_eq⟩

theorem eqvGen_isClosed (g : ℕ) :
    IsClosed {p : Disc×Disc | Relation.EqvGen (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g) p.1 p.2} := by
  have he : {p : Disc×Disc | Relation.EqvGen (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)
    p.1 p.2}=
      {p : Disc×Disc | closedRelation g p.1 p.2} := by
    ext p
    exact ⟨eqvGen_closedRelation,fun h => Quot.eqvGen_exact (closedRelation_quotient_eq h)⟩
  rw [he]
  exact closedRelation_isClosed g

def quotientEqvGenHomeomorph {X : Type*} [TopologicalSpace X] (R : X→X→Prop) :
    Quot R≃ₜQuotient (Relation.EqvGen.setoid R) where
  toFun := Quot.lift (Quotient.mk _) (fun x y h => Quotient.sound (Relation.EqvGen.rel x y h))
  invFun := Quotient.lift (Quot.mk R) (fun _ _ h => Quot.eqvGen_sound h)
  left_inv q := Quot.inductionOn q fun _ => rfl
  right_inv q := Quotient.inductionOn q fun _ => rfl
  continuous_toFun := continuous_quot_lift _ continuous_quotient_mk'
  continuous_invFun := continuous_quot_lift _ continuous_quot_mk

theorem canonicalHandleQuotientT2 (g : ℕ) : T2Space (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)) := by
  let R := Relation.EqvGen.setoid (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent g)
  have hR : IsClosed {p : Disc×Disc | R p.1 p.2} := eqvGen_isClosed g
  let : T2Space (Quotient
    R) := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.closedSetoid_quotient_t2Space R hR
  exact (quotientEqvGenHomeomorph (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent
    g)).isEmbedding.t2Space

theorem canonicalHandleSurfaceT2 (g : ℕ) : T2Space (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleSurface g) := by
  cases g with
  | zero => change T2Space (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1);infer_instance
  | succ g => exact canonicalHandleQuotientT2 (g+1)

theorem canonicalHandleSurfaceCompact (g : ℕ) : CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleSurface g) := by
  cases g with
  | zero => change CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1);infer_instance
  | succ g => change CompactSpace (Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent (g+1)));infer_instance

theorem hasTopologicalGenus_t2Space {X : Type*} [TopologicalSpace X] {g : ℕ}
    (h : _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus X g) : T2Space X := by
  obtain ⟨e⟩ := h
  let : T2Space (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleSurface g) := canonicalHandleSurfaceT2 g
  exact e.isEmbedding.t2Space

theorem hasTopologicalGenus_compactSpace {X : Type*} [TopologicalSpace X] {g : ℕ}
    (h : _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus X g) : CompactSpace X := by
  obtain ⟨e⟩ := h
  let : CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleSurface
    g) := canonicalHandleSurfaceCompact g
  exact e.symm.compactSpace

end LowDimensionalTopology.Geometry.Surfaces.HandleSeparation
