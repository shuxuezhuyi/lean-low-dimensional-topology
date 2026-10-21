/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A matrix takes the closed positive projective cone strictly into its interior,
with its projectively irrelevant overall sign allowed. -/
def StrictConeMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀i j,0<A i j) ∨ (∀i j,A i j<0)

theorem StrictConeMatrix.mul {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : StrictConeMatrix A) (hB : StrictConeMatrix B) : StrictConeMatrix (A*B) := by
  rcases hA with ha | ha <;> rcases hB with hb | hb
  · left;intro i j
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    exact add_pos (mul_pos (ha i 0) (hb 0 j)) (mul_pos (ha i 1) (hb 1 j))
  · right;intro i j
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    exact add_neg (mul_neg_of_pos_of_neg (ha i 0) (hb 0 j)) (mul_neg_of_pos_of_neg (ha i 1) (hb 1 j))
  · right;intro i j
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    exact add_neg (mul_neg_of_neg_of_pos (ha i 0) (hb 0 j)) (mul_neg_of_neg_of_pos (ha i 1) (hb 1 j))
  · left;intro i j
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    exact add_pos (mul_pos_of_neg_of_neg (ha i 0) (hb 0 j)) (mul_pos_of_neg_of_neg (ha i 1) (hb 1 j))

/-- Every determinant-one strict cone map has genuinely hyperbolic trace. -/
theorem StrictConeMatrix.trace_sq_gt_four {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : StrictConeMatrix A) (hd : A.det=1) : 4<(Matrix.trace A)^2 := by
  have hbc : 0<A 0 1*A 1 0 := by
    rcases hA with h | h
    · exact mul_pos (h 0 1) (h 1 0)
    · exact mul_pos_of_neg_of_neg (h 0 1) (h 1 0)
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two]
  nlinarith [sq_nonneg (A 0 0-A 1 1)]

/-- Strict cone transitions along an actually reduced word multiply without introducing any weak endpoint case. -/
theorem strictConeMatrix_word_chain {α : Type*}
    (F P : (α×Bool)→GL (Fin 2) ℝ)
    (htrans : ∀a b,(a.1=b.1→a.2=b.2)→StrictConeMatrix ((P a)⁻¹*F a*P b).val)
    (L : List (α×Bool)) (hL : FreeGroup.IsReduced L)
    (a : α×Bool) (ha : L.head?=some a) (k : α×Bool)
    (hk : ∀b∈L.getLast?,b.1=k.1→b.2=k.2) :
    StrictConeMatrix ((P a)⁻¹*(L.map F).prod*P k).val := by
  induction L generalizing a with
  | nil => simp at ha
  | cons b L ih =>
    have hab : b=a:=Option.some.inj ha
    subst b
    cases L with
    | nil =>
      simp only [List.getLast?_singleton,Option.mem_def,Option.some.injEq] at hk
      simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using
        htrans a k (hk a rfl)
    | cons b L =>
      have hchain : (a.1=b.1→a.2=b.2) ∧ FreeGroup.IsReduced (b::L) := by
        simpa only [FreeGroup.IsReduced,List.isChain_cons_cons] using hL
      have hlast : ∀c∈(b::L).getLast?,c.1=k.1→c.2=k.2 := by
        simpa only [List.getLast?_cons_cons] using hk
      have ht:=ih hchain.2 b rfl hlast
      have hh:=(htrans a b hchain.1).mul ht
      have he : (P a)⁻¹*((a::b::L).map F).prod*P k=
          ((P a)⁻¹*F a*P b)*((P b)⁻¹*((b::L).map F).prod*P k) := by
        simp only [List.map_cons,List.prod_cons]
        group
      rwa [←Matrix.GeneralLinearGroup.coe_mul,←he] at hh

/-- Every nonempty cyclically reduced word satisfying strict cone transitions is genuinely hyperbolic. -/
theorem strictConeMatrix_cyclic_word_trace {α : Type*}
    (f : α→Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : (α×Bool)→GL (Fin 2) ℝ)
    (htrans : ∀a b,(a.1=b.1→a.2=b.2)→
      StrictConeMatrix ((P a)⁻¹*(if a.2 then Matrix.SpecialLinearGroup.mapGL ℝ (f a.1)
        else Matrix.SpecialLinearGroup.mapGL ℝ (f a.1)⁻¹)*P b).val)
    (L : List (α×Bool)) (hL : FreeGroup.IsCyclicallyReduced L) (hne : L≠[]) :
    4<(Matrix.trace (FreeGroup.lift f (FreeGroup.mk L)).val)^2 := by
  let F : (α×Bool)→GL (Fin 2) ℝ:=fun a=>if a.2 then Matrix.SpecialLinearGroup.mapGL ℝ (f a.1)
    else Matrix.SpecialLinearGroup.mapGL ℝ (f a.1)⁻¹
  obtain ⟨a,l,rfl⟩:=List.exists_cons_of_ne_nil hne
  have hlast : ∀b∈(a::l).getLast?,b.1=a.1→b.2=a.2 := by
    intro b hb hba
    exact hL.2 b hb a (by simp) hba
  have hg:=strictConeMatrix_word_chain F P htrans (a::l) hL.1 a rfl a hlast
  let D:=FreeGroup.lift f (FreeGroup.mk (a::l))
  have he : Matrix.SpecialLinearGroup.mapGL ℝ D=((a::l).map F).prod := by
    dsimp only [D]
    rw [FreeGroup.lift_mk,map_list_prod,List.map_map]
    congr 1
    apply List.map_congr_left
    intro b _hb
    dsimp only [Function.comp_def,F]
    cases b.2 <;> simp
  rw [←he] at hg
  have hd : ((P a)⁻¹*Matrix.SpecialLinearGroup.mapGL ℝ D*P a).val.det=1 := by
    change Matrix.det (((P a)⁻¹).val*D.val*(P a).val)=1
    rw [Matrix.det_units_conj',D.det_coe]
  have ht:=hg.trace_sq_gt_four hd
  change 4<(Matrix.trace (((P a)⁻¹).val*D.val*(P a).val))^2 at ht
  rwa [Matrix.trace_units_conj'] at ht

/-- A genuine real lift with trace square greater than four cannot project to identity. -/
theorem realSLMobius_ne_one_of_trace_sq_gt_four
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4<(Matrix.trace A.val)^2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1 := by
  intro he
  have h1 : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=(4:ℂ) := by
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace (1:Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    norm_num [Matrix.trace_fin_two] at hh
    exact hh
  have hh:=congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,h1] at hh
  have hr : (Matrix.trace A.val)^2=4:=Complex.ofReal_injective hh
  linarith

/-- Strict cone transitions prove the full generated group purely hyperbolic,
not merely the displayed generators. All free words are cyclically reduced inside the proof. -/
theorem purelyHyperbolic_of_strictCone_transitions {α : Type*}
    (f : α→Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : (α×Bool)→GL (Fin 2) ℝ)
    (htrans : ∀a b,(a.1=b.1→a.2=b.2)→
      StrictConeMatrix ((P a)⁻¹*(if a.2 then Matrix.SpecialLinearGroup.mapGL ℝ (f a.1)
        else Matrix.SpecialLinearGroup.mapGL ℝ (f a.1)⁻¹)*P b).val) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsPurelyHyperbolic (Subgroup.closure (Set.range (fun a=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (f a)))) := by
  classical
  intro g hgne
  have hrange:=FreeGroup.range_lift_eq_closure (f:=fun a=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    (f a))
  have hgmem : g.val∈(FreeGroup.lift (fun a=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (f a))).range:=by
    rw [hrange]
    exact g.property
  obtain ⟨w,hw⟩:=hgmem
  let L:=w.toWord
  let C:=FreeGroup.reduceCyclically L
  let U:=FreeGroup.reduceCyclically.conjugator L
  have hsplit : w=FreeGroup.mk U*FreeGroup.mk C*(FreeGroup.mk U)⁻¹ := by
    rw [FreeGroup.inv_mk,FreeGroup.mul_mk,FreeGroup.mul_mk]
    rw [FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically]
    exact (FreeGroup.mk_toWord (x:=w)).symm
  let π:=FreeGroup.lift (fun a=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (f a))
  have hπ : π=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.comp (FreeGroup.lift f) := by
    apply FreeGroup.ext_hom
    intro a
    simp [π]
  have hrep : g.val=π (FreeGroup.mk U)*π (FreeGroup.mk C)*(π (FreeGroup.mk U))⁻¹ := by
    rw [←hw,hsplit,map_mul,map_mul,map_inv]
  have hCne : C≠[] := by
    intro he
    rw [he] at hrep
    simp only [←FreeGroup.one_eq_mk,map_one,mul_one,mul_inv_cancel] at hrep
    exact hgne hrep
  have hCR : FreeGroup.IsCyclicallyReduced C:=
    FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
  have ht:=strictConeMatrix_cyclic_word_trace f P htrans C hCR hCne
  have hCM : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (π (FreeGroup.mk C)) := by
    rw [hπ,MonoidHom.comp_apply]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
      (realSLMobius_ne_one_of_trace_sq_gt_four _ ht)).mpr ht
  rw [hrep]
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation _ _).mpr hCM

/-- The first explicit real boost, with positive eigenvalue parameter. -/
def schottkyFirstSL (l : ℝ) (hl : 0<l) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![l,0;0,l⁻¹],by simp [Matrix.det_fin_two,hl.ne']⟩

/-- The second real boost has the genuinely perpendicular invariant axis. -/
def schottkySecondSL (l : ℝ) (hl : 0<l) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![(l+l⁻¹)/2,-(l-l⁻¹)/2;-(l-l⁻¹)/2,(l+l⁻¹)/2],by
    simp only [Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    field_simp
    ring⟩

/-- The two actual boosts, before their complete word property is proved. -/
def schottkyGeneratorsSL (l : ℝ) (hl : 0<l) (b : Bool) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  if b then schottkySecondSL l hl else schottkyFirstSL l hl

/-- Four actual real projective cone frames around the four distinct axis endpoints. -/
def schottkyFrameMatrix (r : ℝ) (a : Bool×Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  match a.1,a.2 with
  | false,true => !![r,r;1,-1]
  | true,true => !![r+1,r-1;1-r,-r-1]
  | false,false => !![1,-1;-r,-r]
  | true,false => !![1-r,-r-1;-r-1,1-r]

def schottkyFrame (r : ℝ) (hr : 0<r) (a : Bool×Bool) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (schottkyFrameMatrix r a) (by
    rcases a with ⟨a,b⟩
    cases a <;> cases b <;>
      simp only [schottkyFrameMatrix,Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one]
    all_goals nlinarith)

/-- The twelve genuinely noncancelling cone transitions are strict as soon as the four boundary geodesics separate. -/
theorem schottky_strictCone_transitions (r l : ℝ) (hr : 0<r) (hroot : r^2-2*r-1=0)
    (hlr : r<l) :
    ∀a b : Bool×Bool,(a.1=b.1→a.2=b.2)→
      StrictConeMatrix ((schottkyFrame r hr a)⁻¹*
        (if a.2 then Matrix.SpecialLinearGroup.mapGL ℝ (schottkyGeneratorsSL l (lt_trans hr hlr) a.1)
          else Matrix.SpecialLinearGroup.mapGL ℝ (schottkyGeneratorsSL l (lt_trans hr hlr) a.1)⁻¹)*
        schottkyFrame r hr b).val := by
  have hr1 : 1<r := by
    by_contra! hn
    have hmul:=mul_nonneg hr.le (sub_nonneg.mpr hn)
    nlinarith
  have hl : 0<l:=lt_trans hr hlr
  have hl1 : 1<l:=lt_trans hr1 hlr
  have hsq : r^2<l^2:=(sq_lt_sq₀ hr.le hl.le).mpr hlr
  intro a b hab
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at *
  all_goals try (simp at hab)
  apply Or.inl
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inr
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inr
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inl
  rotate_left
  apply Or.inl
  rotate_left
  all_goals intro i j
  all_goals fin_cases i <;> fin_cases j
  all_goals
    simp only [Matrix.GeneralLinearGroup.coe_mul,Matrix.GeneralLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      schottkyFrame,Matrix.GeneralLinearGroup.val_mkOfDetNeZero,schottkyFrameMatrix,
      schottkyGeneratorsSL,Bool.false_eq_true,ite_false,ite_true,
      schottkyFirstSL,schottkySecondSL,
      Matrix.inv_def,Matrix.det_fin_two,Matrix.adjugate_fin_two,Matrix.smul_apply,smul_eq_mul,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    norm_num [Matrix.SpecialLinearGroup.map,Ring.inverse_eq_inv]
  all_goals
    ring_nf
    field_simp
    ring_nf
    try nlinarith

/-- The critical exact eigenvalue at which the ideal quadrilateral degenerates. -/
def schottkyThreshold : ℝ:=1+Real.sqrt 2

theorem schottkyThreshold_pos : 0<schottkyThreshold := by unfold schottkyThreshold;positivity

theorem schottkyThreshold_quadratic : schottkyThreshold^2-2*schottkyThreshold-1=0 := by
  unfold schottkyThreshold
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

/-- The actual group generated by the two displayed geometric boosts. -/
def schottkyGroup (l : ℝ) (hl : 0<l) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  Subgroup.closure (Set.range (fun b=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    (schottkyGeneratorsSL l hl b)))

/-- Every nonidentity element of the actual explicit group is hyperbolic for every parameter above the critical value. -/
theorem schottkyGroup_purelyHyperbolic (l : ℝ) (hl : schottkyThreshold<l) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsPurelyHyperbolic (schottkyGroup l (lt_trans schottkyThreshold_pos hl)) := by
  exact purelyHyperbolic_of_strictCone_transitions _ _
    (schottky_strictCone_transitions schottkyThreshold l schottkyThreshold_pos schottkyThreshold_quadratic hl)

/-- The two explicit boosts are genuinely hyperbolic, before any word argument. -/
theorem schottkyGeneratorsSL_hyperbolic (l : ℝ) (hl1 : 1<l) (b : Bool) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyGeneratorsSL l (by linarith) b)) := by
  have hl : 0<l:=by linarith
  have hi : l⁻¹<1:=(inv_lt_one₀ hl).mpr hl1
  have hd : (l+l⁻¹)^2>4 := by
    have hm : l*l⁻¹=1:=mul_inv_cancel₀ hl.ne'
    have hpos : 0<(l-l⁻¹)^2:=sq_pos_of_pos (by linarith)
    nlinarith
  have htrace : (Matrix.trace (schottkyGeneratorsSL l (by linarith) b).val)^2>4 := by
    cases b <;> simp only [schottkyGeneratorsSL,Bool.false_eq_true,ite_false,ite_true,
      schottkyFirstSL,schottkySecondSL,Matrix.trace_fin_two,Matrix.SpecialLinearGroup.coe_mk,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    · exact hd
    · convert hd using 1; ring
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (realSLMobius_ne_one_of_trace_sq_gt_four _ htrace)).mpr htrace

/-- No-common-fixed-point loxodromics generate an actual non-elementary group without a discreteness assumption. -/
theorem loxodromic_pair_nonElementary_of_no_common_fixed
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic g)
    (hn : ¬∃p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,f.val p=p ∧ g.val p=p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  intro he
  let K:=Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hfm : f∈K:=Subgroup.subset_closure (Set.mem_insert _ _)
  have hgm : g∈K:=Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨p,hp⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_loxodromic_boundary_finite_orbit K he f hfm hf
  exact hn ⟨p,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_boundary_orbit_fixed_by_loxodromic K f hfm hf
    p hp,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_boundary_orbit_fixed_by_loxodromic K g hgm hg p hp⟩

/-- The literal first boost fixes zero and infinity. -/
theorem schottkyFirstSL_fixed_endpoints (l : ℝ) (hl : 0<l) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyFirstSL l hl)).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyFirstSL l hl)).val ∞=∞ := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius,MonoidHom.comp_apply,_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action]
  constructor
  · rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
    norm_num [schottkyFirstSL,Matrix.SpecialLinearGroup.toGL,Complex.ofReal_ne_zero.mpr hl.ne']
  · rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
    simp [schottkyFirstSL,Matrix.SpecialLinearGroup.toGL]

/-- The second boost fixes neither endpoint of the first boost's actual axis. -/
theorem schottkySecondSL_no_fixed_special (l : ℝ) (hl1 : 1<l) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkySecondSL l (by linarith))).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)≠((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkySecondSL l (by linarith))).val ∞≠∞ := by
  have hl : 0<l:=by linarith
  have hi : l⁻¹<1:=(inv_lt_one₀ hl).mpr hl1
  have hsum : (l:ℂ)+(l:ℂ)⁻¹≠0 := by
    exact_mod_cast (add_pos hl (inv_pos.mpr hl)).ne'
  have hdiff : (l:ℂ)⁻¹-(l:ℂ)≠0 := by
    exact_mod_cast (show l⁻¹-l≠0 by linarith)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius,MonoidHom.comp_apply,_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action]
  constructor
  · rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
    simp [schottkySecondSL,Matrix.SpecialLinearGroup.toGL,hsum,hdiff]
  · rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
    simp [schottkySecondSL,Matrix.SpecialLinearGroup.toGL,hdiff]

/-- The explicit two boosts generate a genuinely non-elementary group for every l>1. -/
theorem schottkyGeneratorsSL_nonElementary (l : ℝ) (hl1 : 1<l) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyFirstSL l (by linarith)),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkySecondSL l (by linarith))}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  have hA:=schottkyGeneratorsSL_hyperbolic l hl1 false
  have hB:=schottkyGeneratorsSL_hyperbolic l hl1 true
  simp only [schottkyGeneratorsSL,Bool.false_eq_true,ite_false,ite_true] at hA hB
  apply loxodromic_pair_nonElementary_of_no_common_fixed _ _ hA.1 hB.1
  rintro ⟨p,hpA,hpB⟩
  have hfix:=schottkyFirstSL_fixed_endpoints l (by linarith)
  have hnot:=schottkySecondSL_no_fixed_special l hl1
  by_cases hp0 : p=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  · exact hnot.1 (by simpa only [hp0] using hpB)
  by_cases hpi : p=∞
  · exact hnot.2 (by simpa only [hpi] using hpB)
  exact hA.1.1 (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_three_fixed _
    ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∞ p
    (OnePoint.coe_ne_infty _) (Ne.symm hp0) (Ne.symm hpi) hfix.1 hfix.2 hpA)

/-- Both explicit boosts have the same actual half-displacement at the native point i. -/
theorem schottkyGeneratorsSL_displacement_I (l : ℝ) (hl1 : 1<l) (b : Bool) :
    Real.sinh (dist UpperHalfPlane.I (schottkyGeneratorsSL l (by linarith) b • UpperHalfPlane.I)/2)=
      (l-l⁻¹)/2 := by
  have hl : 0<l:=by linarith
  have hi : l⁻¹<1:=(inv_lt_one₀ hl).mpr hl1
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_half_displacement_polynomial]
  cases b <;>
    simp only [schottkyGeneratorsSL,Bool.false_eq_true,ite_false,ite_true,schottkyFirstSL,schottkySecondSL,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  all_goals push_cast
  · change ‖(0:ℂ)*Complex.I^2+((l⁻¹:ℂ)-(l:ℂ))*Complex.I-0‖/(2*1)=(l-l⁻¹)/2
    rw [zero_mul,zero_add,sub_zero,norm_mul,Complex.norm_I,mul_one]
    rw [show (l:ℂ)⁻¹-(l:ℂ)=((l⁻¹-l:ℝ):ℂ) by push_cast;rfl,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : l⁻¹-l<0)]
    ring
  · change ‖-((l:ℂ)-(l:ℂ)⁻¹)/2*Complex.I^2+
        (((l:ℂ)+(l:ℂ)⁻¹)/2-((l:ℂ)+(l:ℂ)⁻¹)/2)*Complex.I- -((l:ℂ)-(l:ℂ)⁻¹)/2‖/(2*1)=(l-l⁻¹)/2
    have he : -((l:ℂ)-(l:ℂ)⁻¹)/2*Complex.I^2+
        (((l:ℂ)+(l:ℂ)⁻¹)/2-((l:ℂ)+(l:ℂ)⁻¹)/2)*Complex.I- -((l:ℂ)-(l:ℂ)⁻¹)/2=((l-l⁻¹:ℝ):ℂ) := by
      rw [Complex.I_sq]
      push_cast
      ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0<l-l⁻¹)]
    norm_num

/-- The explicit Boolean generating range is exactly the original two-element generating set. -/
theorem schottkyGroup_eq_pair (l : ℝ) (hl : 0<l) : schottkyGroup l hl=
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyFirstSL l hl),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkySecondSL l hl)}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  unfold schottkyGroup
  congr 1
  ext g
  constructor
  · rintro ⟨b,rfl⟩
    cases b <;> simp [schottkyGeneratorsSL]
  · rintro (rfl | rfl)
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩

/-- Both displayed actual generators lie in the genuine generated group. -/
theorem schottkyGeneratorsSL_mem_group (l : ℝ) (hl : 0<l) (b : Bool) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyGeneratorsSL l hl b)∈schottkyGroup l hl :=
  Subgroup.subset_closure ⟨b,rfl⟩

/-- The actual Schottky family is non-elementary throughout the strictly separated regime. -/
theorem schottkyGroup_nonElementary (l : ℝ) (hl : schottkyThreshold<l) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (schottkyGroup l (lt_trans schottkyThreshold_pos hl)) := by
  rw [schottkyGroup_eq_pair]
  apply schottkyGeneratorsSL_nonElementary
  unfold schottkyThreshold at hl
  linarith [Real.sqrt_nonneg (2:ℝ)]

/-- Every element has an actual real determinant-one lift, not just the two original generators. -/
theorem schottkyGroup_le_realSL_range (l : ℝ) (hl : 0<l) :
    schottkyGroup l hl≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
  apply (Subgroup.closure_le _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range).mpr
  rintro g ⟨b,rfl⟩
  exact ⟨schottkyGeneratorsSL l hl b,rfl⟩

/-- The same genuine open half-disc is invariant under the whole explicit group. -/
theorem schottkyGroup_invariantDisc (l : ℝ) (hl : 0<l) : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc (schottkyGroup l hl) := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.standardComplexHalfDisc,_root_.LowDimensionalTopology.Geometry.Mobius.standardComplexHalfDisc_isDisc,?_⟩
  intro f
  obtain ⟨A,hA⟩:=schottkyGroup_le_realSL_range l hl f.property
  exact hA ▸ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_preserves_halfDisc A

/-- Discreteness is a consequence of the proved whole-group property and non-elementarity. -/
theorem schottkyGroup_discrete (l : ℝ) (hl : schottkyThreshold<l) :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (schottkyGroup l (lt_trans
      schottkyThreshold_pos hl)) :=
  (schottkyGroup_purelyHyperbolic l hl).discrete (schottkyGroup_nonElementary l hl)

/-- The critical exact half-displacement equals one. -/
theorem schottkyThreshold_half_displacement : (schottkyThreshold-schottkyThreshold⁻¹)/2=1 := by
  field_simp [schottkyThreshold_pos.ne']
  nlinarith [schottkyThreshold_quadratic]

/-- The two native displacement factors approach one from a family of genuine purely hyperbolic groups. -/
theorem schottky_displacement_product_tendsto :
    Filter.Tendsto (fun l:ℝ=>((l-l⁻¹)/2)^2)
      (nhdsWithin schottkyThreshold (Ioi schottkyThreshold)) (nhds 1) := by
  have hc : ContinuousAt (fun l:ℝ=>((l-l⁻¹)/2)^2) schottkyThreshold :=
    ((continuousAt_id.sub (continuousAt_inv₀ schottkyThreshold_pos.ne')).div_const 2).pow 2
  have ht:=hc.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi schottkyThreshold))
  simpa only [schottkyThreshold_half_displacement,one_pow] using ht

/-- Any constant above one is violated by a parameter in the strictly separated regime. -/
theorem schottky_exists_product_parameter (C : ℝ) (hC : 1<C) :
    ∃l : ℝ,schottkyThreshold<l ∧ ((l-l⁻¹)/2)^2<C := by
  have he:=schottky_displacement_product_tendsto.eventually (gt_mem_nhds hC)
  have hi : ∀ᶠl in nhdsWithin schottkyThreshold (Ioi schottkyThreshold),schottkyThreshold<l :=
    self_mem_nhdsWithin
  exact (hi.and he).exists

/-- The exact maximum-displacement scalar approaches the sharp constant simultaneously. -/
theorem schottky_maximum_displacement_tendsto :
    Filter.Tendsto (fun l:ℝ=>2*Real.arsinh ((l-l⁻¹)/2))
      (nhdsWithin schottkyThreshold (Ioi schottkyThreshold)) (nhds (2*Real.arsinh 1)) := by
  have hc : ContinuousAt (fun l:ℝ=>2*Real.arsinh ((l-l⁻¹)/2)) schottkyThreshold :=
    continuousAt_const.mul (Real.continuous_arsinh.continuousAt.comp
      ((continuousAt_id.sub (continuousAt_inv₀ schottkyThreshold_pos.ne')).div_const 2))
  have ht:=hc.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi schottkyThreshold))
  simpa only [schottkyThreshold_half_displacement] using ht

/-- Any proposed larger maximum-displacement constant is violated above the critical parameter. -/
theorem schottky_exists_maximum_parameter (C : ℝ) (hC : 2*Real.arsinh 1<C) :
    ∃l : ℝ,schottkyThreshold<l ∧ 2*Real.arsinh ((l-l⁻¹)/2)<C := by
  have he:=schottky_maximum_displacement_tendsto.eventually (gt_mem_nhds hC)
  have hi : ∀ᶠl in nhdsWithin schottkyThreshold (Ioi schottkyThreshold),schottkyThreshold<l :=
    self_mem_nhdsWithin
  exact (hi.and he).exists

/-- Purely hyperbolic, non-elementary, discrete actual groups approach the displacement-product lower bound one. -/
theorem purelyHyperbolic_product_sharpness (C : ℝ) (hC : 1<C) :
    ∃l : ℝ,∃hl : schottkyThreshold<l,
      let hp:=lt_trans schottkyThreshold_pos hl
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsPurelyHyperbolic (schottkyGroup l
        hp) ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (schottkyGroup l hp) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (schottkyGroup l
        hp) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc (schottkyGroup l hp) ∧
      Real.sinh (dist UpperHalfPlane.I (schottkyFirstSL l hp • UpperHalfPlane.I)/2)*
        Real.sinh (dist UpperHalfPlane.I (schottkySecondSL l hp • UpperHalfPlane.I)/2)<C := by
  obtain ⟨l,hl,hprod⟩:=schottky_exists_product_parameter C hC
  have hl1 : 1<l := by
    unfold schottkyThreshold at hl
    linarith [Real.sqrt_nonneg (2:ℝ)]
  refine ⟨l,hl,schottkyGroup_purelyHyperbolic l hl,schottkyGroup_nonElementary l hl,
    schottkyGroup_discrete l hl,schottkyGroup_invariantDisc l _,?_⟩
  have ha:=schottkyGeneratorsSL_displacement_I l hl1 false
  have hb:=schottkyGeneratorsSL_displacement_I l hl1 true
  simp only [schottkyGeneratorsSL,Bool.false_eq_true,ite_false,ite_true] at ha hb
  rw [ha,hb]
  simpa only [pow_two] using hprod

/-- The same genuine purely hyperbolic family proves the larger-displacement constant cannot be increased. -/
theorem purelyHyperbolic_maximum_sharpness (C : ℝ) (hC : 2*Real.arsinh 1<C) :
    ∃l : ℝ,∃hl : schottkyThreshold<l,
      let hp:=lt_trans schottkyThreshold_pos hl
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsPurelyHyperbolic (schottkyGroup l
        hp) ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (schottkyGroup l hp) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (schottkyGroup l
        hp) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc (schottkyGroup l hp) ∧
      max (dist UpperHalfPlane.I (schottkyFirstSL l hp • UpperHalfPlane.I))
        (dist UpperHalfPlane.I (schottkySecondSL l hp • UpperHalfPlane.I))<C := by
  obtain ⟨l,hl,hmax⟩:=schottky_exists_maximum_parameter C hC
  have hl1 : 1<l := by
    unfold schottkyThreshold at hl
    linarith [Real.sqrt_nonneg (2:ℝ)]
  refine ⟨l,hl,schottkyGroup_purelyHyperbolic l hl,schottkyGroup_nonElementary l hl,
    schottkyGroup_discrete l hl,schottkyGroup_invariantDisc l _,?_⟩
  have ha:=congrArg Real.arsinh (schottkyGeneratorsSL_displacement_I l hl1 false)
  have hb:=congrArg Real.arsinh (schottkyGeneratorsSL_displacement_I l hl1 true)
  simp only [schottkyGeneratorsSL,Bool.false_eq_true,ite_false,ite_true,Real.arsinh_sinh] at ha hb
  have hA : dist UpperHalfPlane.I (schottkyFirstSL l (lt_trans schottkyThreshold_pos hl) • UpperHalfPlane.I)=
      2*Real.arsinh ((l-l⁻¹)/2) := by linarith
  have hB : dist UpperHalfPlane.I (schottkySecondSL l (lt_trans schottkyThreshold_pos hl) • UpperHalfPlane.I)=
      2*Real.arsinh ((l-l⁻¹)/2) := by linarith
  rwa [hA,hB,max_self]

end LowDimensionalTopology.Geometry.Fuchsian
