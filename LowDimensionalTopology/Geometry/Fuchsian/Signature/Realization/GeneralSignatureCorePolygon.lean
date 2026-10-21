module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofinitePolygonLowerSharpness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped BigOperators Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

def generalCoreDeficit (g : ℕ) (orders : List ℕ) (s t : ℕ) : ℝ :=
  2*(g:ℝ)-2+s+t+(orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum

def generalCoreBaseCount (g : ℕ) (orders : List ℕ) (s t : ℕ) : ℕ :=
  4*g+orders.length+s+t

def generalCoreBaseAngle (g : ℕ) (orders : List ℕ) (s t : ℕ) : ℝ :=
  2*Real.pi/(generalCoreBaseCount g orders s t:ℝ)

/-- Each boundary end contributes two actual right corners separated by its
unpaired geodesic cut side. A cusp still contributes its actual zero corner. -/
def generalCoreAngles (g : ℕ) (orders : List ℕ) (s t : ℕ) : List ℝ :=
  let β:=generalCoreBaseAngle g orders s t
  List.replicate (4*g) β ++ cofiniteConstructionMarkAngles β orders ++
    (List.replicate s [β,0]).flatten ++ (List.replicate t [β,Real.pi/2,Real.pi/2]).flatten

theorem generalCore_cone_sum (orders : List ℕ) :
    (orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum=
      (orders.length:ℝ)-(orders.map (fun m:ℕ=>1/(m:ℝ))).sum := by
  induction orders with
  | nil=>simp
  | cons m ms ih=>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [ih]
    ring

theorem generalCore_base_count (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (h : 0<generalCoreDeficit g orders s t) : 3≤generalCoreBaseCount g orders s t := by
  have hrec : 0≤(orders.map (fun m:ℕ=>1/(m:ℝ))).sum :=
    List.sum_nonneg (by intro x hx;obtain ⟨m,_,rfl⟩:=List.mem_map.mp hx;positivity)
  by_contra hn
  have hg : g=0:=by dsimp only [generalCoreBaseCount] at hn;omega
  have hm : orders.length+s+t≤2:=by dsimp only [generalCoreBaseCount] at hn;omega
  have hmR : (orders.length:ℝ)+s+t≤2:=by exact_mod_cast hm
  rw [generalCoreDeficit,generalCore_cone_sum,hg] at h
  norm_num only [Nat.cast_zero,mul_zero,zero_sub] at h
  linarith only [h,hrec,hmR]

theorem generalCore_base_angle_mem (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (h : 0<generalCoreDeficit g orders s t) :
    generalCoreBaseAngle g orders s t∈Ico (0:ℝ) Real.pi := by
  have hB : (3:ℝ)≤generalCoreBaseCount g orders s t:=by
    exact_mod_cast generalCore_base_count g orders s t h
  constructor
  · dsimp only [generalCoreBaseAngle];positivity
  · dsimp only [generalCoreBaseAngle]
    apply (div_lt_iff₀ (by linarith only [hB] : (0:ℝ)<generalCoreBaseCount g orders s t)).mpr
    nlinarith only [hB,Real.pi_pos]

theorem generalCore_mark_angles_mem (β : ℝ) (hβ : β∈Ico (0:ℝ) Real.pi)
    (orders : List ℕ) (ho : ∀m∈orders,2≤m) :
    ∀a∈cofiniteConstructionMarkAngles β orders,a∈Ico (0:ℝ) Real.pi := by
  induction orders with
  | nil=>simp [cofiniteConstructionMarkAngles]
  | cons m ms ih=>
    have hm:=ho m (by simp)
    have ht : ∀n∈ms,2≤n:=fun n hn=>ho n (List.mem_cons_of_mem m hn)
    by_cases hm2 : m=2
    · simpa only [cofiniteConstructionMarkAngles,hm2,ite_true,List.mem_cons] using
        (show ∀a:ℝ,a=β ∨ a∈cofiniteConstructionMarkAngles β ms→a∈Ico (0:ℝ) Real.pi from
          fun a ha=>ha.elim (fun he=>he ▸ hβ) (ih ht a))
    · intro a ha
      simp only [cofiniteConstructionMarkAngles,hm2,ite_false,List.mem_cons] at ha
      rcases ha with rfl|rfl|ha
      · exact hβ
      · have hmR : (3:ℝ)≤m:=by exact_mod_cast (by omega : 3≤m)
        constructor
        · dsimp only [cofiniteConstructionConeAngle];positivity
        · dsimp only [cofiniteConstructionConeAngle]
          apply (div_lt_iff₀ (by linarith only [hmR] : (0:ℝ)<m)).mpr
          nlinarith only [hmR,Real.pi_pos]
      · exact ih ht a ha

theorem generalCore_angles_mem (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀m∈orders,2≤m) (h : 0<generalCoreDeficit g orders s t) :
    ∀a∈generalCoreAngles g orders s t,a∈Ico (0:ℝ) Real.pi := by
  let β:=generalCoreBaseAngle g orders s t
  have hβ : β∈Ico (0:ℝ) Real.pi:=generalCore_base_angle_mem g orders s t h
  have hf (n:ℕ) (block:List ℝ) (hb:∀a∈block,a∈Ico (0:ℝ) Real.pi) :
      ∀a∈(List.replicate n block).flatten,a∈Ico (0:ℝ) Real.pi := by
    intro a ha
    obtain ⟨l,hl,ha⟩:=List.mem_flatten.mp ha
    exact hb a ((List.eq_of_mem_replicate hl) ▸ ha)
  intro a ha
  change a∈List.replicate (4*g) β ++ cofiniteConstructionMarkAngles β orders ++
    (List.replicate s [β,0]).flatten ++ (List.replicate t [β,Real.pi/2,Real.pi/2]).flatten at ha
  simp only [List.mem_append] at ha
  rcases ha with ((ha|ha)|ha)|ha
  · exact (List.eq_of_mem_replicate ha) ▸ hβ
  · exact generalCore_mark_angles_mem β hβ orders ho a ha
  · apply hf s [β,0] ?_ a ha
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact hβ
    · exact ⟨le_rfl,Real.pi_pos⟩
  · apply hf t [β,Real.pi/2,Real.pi/2] ?_ a ha
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
    rcases hx with rfl|rfl
    · exact hβ
    · constructor <;> linarith only [Real.pi_pos]

def generalCoreAngleCharge (angles : List ℝ) : ℝ := (angles.length:ℝ)*Real.pi-angles.sum

theorem generalCoreAngleCharge_append (a b : List ℝ) :
    generalCoreAngleCharge (a++b)=generalCoreAngleCharge a+generalCoreAngleCharge b := by
  simp only [generalCoreAngleCharge,List.length_append,Nat.cast_add,List.sum_append]
  ring

theorem generalCoreAngleCharge_repeated_block (n : ℕ) (block : List ℝ) :
    generalCoreAngleCharge (List.replicate n block).flatten=(n:ℝ)*generalCoreAngleCharge block := by
  induction n with
  | zero=>simp [generalCoreAngleCharge]
  | succ n ih=>
    simp only [List.replicate_succ,List.flatten_cons,generalCoreAngleCharge_append,ih,Nat.cast_add,Nat.cast_one]
    ring

theorem generalCoreAngleCharge_marks (β : ℝ) (orders : List ℕ) :
    generalCoreAngleCharge (cofiniteConstructionMarkAngles β orders)=
      (orders.length:ℝ)*(2*Real.pi-β)-2*Real.pi*(orders.map (fun m:ℕ=>1/(m:ℝ))).sum := by
  induction orders with
  | nil=>simp [cofiniteConstructionMarkAngles,generalCoreAngleCharge]
  | cons m ms ih=>
    by_cases hm : m=2
    · subst m
      simp only [cofiniteConstructionMarkAngles,ite_true,generalCoreAngleCharge,
        List.length_cons,List.sum_cons,List.map_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
      norm_num only [Nat.cast_ofNat]
      linarith only [ih]
    · simp only [cofiniteConstructionMarkAngles,hm,ite_false,generalCoreAngleCharge,
        List.length_cons,List.sum_cons,List.map_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
      dsimp only [cofiniteConstructionConeAngle]
      simp only [div_eq_mul_inv] at ih ⊢
      linarith only [ih]

theorem generalCore_angles_defect (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (hB : 0<generalCoreBaseCount g orders s t) :
    (((generalCoreAngles g orders s t).length:ℝ)-2)*Real.pi-
      (generalCoreAngles g orders s t).sum=2*Real.pi*generalCoreDeficit g orders s t := by
  let β:=generalCoreBaseAngle g orders s t
  have hbase : (generalCoreBaseCount g orders s t:ℝ)*β=2*Real.pi:=by
    exact mul_div_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt hB))
  have hcharge : generalCoreAngleCharge (generalCoreAngles g orders s t)=
      (4*g:ℕ)*(Real.pi-β)+(orders.length:ℝ)*(2*Real.pi-β)-
        2*Real.pi*(orders.map (fun m:ℕ=>1/(m:ℝ))).sum+
        (s:ℝ)*(2*Real.pi-β)+(t:ℝ)*(2*Real.pi-β) := by
    simp only [generalCoreAngles,generalCoreAngleCharge_append,
      generalCoreAngleCharge_marks,generalCoreAngleCharge_repeated_block]
    simp only [generalCoreAngleCharge,List.length_replicate,List.sum_replicate,nsmul_eq_mul,
      List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,Nat.cast_zero,
      Nat.cast_add,Nat.cast_one,add_zero]
    dsimp only [β]
    ring
  dsimp only [generalCoreAngleCharge] at hcharge
  dsimp only [generalCoreDeficit]
  rw [generalCore_cone_sum]
  dsimp only [generalCoreBaseCount] at hbase
  push_cast at hbase hcharge
  nlinarith only [hbase,hcharge]

def generalCoreTheta (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    Fin (generalCoreAngles g orders s t).length→ℝ := fun i=>(generalCoreAngles g orders s t)[i]

theorem generalCoreTheta_mem (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀m∈orders,2≤m) (h : 0<generalCoreDeficit g orders s t) :
    ∀i,generalCoreTheta g orders s t i∈Ico (0:ℝ) Real.pi := by
  intro i
  exact generalCore_angles_mem g orders s t ho h _ (List.getElem_mem _)

/-- Actual ordered convex cut-core polygons exist for every positive original
signature deficit, with genuine cusp and right-corner boundary blocks. -/
theorem generalCore_polygon_exists (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀m∈orders,2≤m) (h : 0<generalCoreDeficit g orders s t) :
    ∃(d:ℝ)(hd:0<d)(_hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d=Real.pi),
      ∃Q:_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon (generalCoreAngles g orders s t).length,Q.IsConvex ∧ 0∈Q.interior ∧
        Q.vertices=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex (generalCoreTheta g orders s t) d
          (generalCoreTheta_mem g orders s t ho h) hd ∧
        (∀i,Q.angle i=generalCoreTheta g orders s t i) := by
  let θ:=generalCoreTheta g orders s t
  have hθ:=generalCoreTheta_mem g orders s t ho h
  have hsum : (∑i,θ i)<(((generalCoreAngles g orders s t).length:ℝ)-2)*Real.pi := by
    have he : (∑i,θ i)=(generalCoreAngles g orders s t).sum:=by
      rw [←List.sum_ofFn]
      apply congrArg List.sum
      exact List.ofFn_getElem
    rw [he]
    have hdef:=generalCore_angles_defect g orders s t (by
      have hb:=generalCore_base_count g orders s t h;omega)
    have hp : 0<2*Real.pi*generalCoreDeficit g orders s t:=by positivity
    linarith only [hdef,hp]
  obtain ⟨d,hd,hb⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance_exists_positive θ hθ hsum
  exact ⟨d,hd,hb,_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_origin_mem θ d hθ hd hb,rfl,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb⟩

end LowDimensionalTopology.Geometry.Fuchsian
