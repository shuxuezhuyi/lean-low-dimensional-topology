/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleIntegralDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeClosedDirichletCover
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.HyperbolicPencils
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Vertical shearing by an arbitrary continuous graph is a genuine ambient homeomorphism. -/
def continuousGraphShear (f : ℝ → ℝ) (hf : Continuous f) : ℂ ≃ₜ ℝ × ℝ where
  toFun z := (z.re,z.im-f z.re)
  invFun p := ⟨p.1,p.2+f p.1⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst)))

/-- Relative closure in the actual upper half-plane of a continuous graph strip. -/
theorem halfPlaneAboveGraph_closure (f : ℝ→ℝ) (hf : Continuous f) (a b : ℝ) (hab : a<b) :
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph f (Ioo a b)) =
      {z : ℍ | z.re∈Icc a b ∧ f z.re≤z.im} := by
  let F : ℍ→ℝ×ℝ := fun z=>continuousGraphShear f hf (z:ℂ)
  have ho : IsOpenMap F := (continuousGraphShear f hf).isOpenMap.comp
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  have hc : Continuous F := (continuousGraphShear f hf).continuous.comp UpperHalfPlane.continuous_coe
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph f (Ioo a b)=F ⁻¹' (Ioo a b ×ˢ Ioi 0) := by
    ext z
    change (z.re∈Ioo a b ∧ f z.re<z.im) ↔ (z.re∈Ioo a b ∧ 0<z.im-f z.re)
    rw [sub_pos]
  rw [hA,←ho.preimage_closure_eq_closure_preimage hc,closure_prod_eq,closure_Ioo hab.ne,closure_Ioi]
  ext z
  change (z.re∈Icc a b ∧ 0≤z.im-f z.re) ↔ (z.re∈Icc a b ∧ f z.re≤z.im)
  rw [sub_nonneg]

/-- For the genuine unit-circle lower graph, the weak boundary is the actual exterior circle strip. -/
theorem halfPlane_unitCircleGraph_closure (a b : ℝ) (hab : a<b) :
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2)) (Ioo a b)) =
      {z : ℍ | z.re∈Icc a b ∧ 1≤‖(z:ℂ)‖^2} := by
  rw [halfPlaneAboveGraph_closure _ (by fun_prop) a b hab]
  ext z
  change (z.re∈Icc a b ∧ Real.sqrt (1-z.re^2)≤z.im) ↔
    (z.re∈Icc a b ∧ 1≤‖(z:ℂ)‖^2)
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  change (z.re∈Icc a b ∧ Real.sqrt (1-z.re^2)≤z.im) ↔
    (z.re∈Icc a b ∧ 1≤z.re*z.re+z.im*z.im)
  have hz := z.im_pos
  rw [Real.sqrt_le_iff]
  constructor
  · rintro ⟨hx,_,hy⟩
    exact ⟨hx,by nlinarith⟩
  · rintro ⟨hx,hy⟩
    exact ⟨hx,hz.le,by nlinarith⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The original prescribed ideal triangle is exactly its literal vertical strip above the unit circle. -/
theorem prescribedIdealHTriangle_interior_graph (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) :
    (prescribedIdealHTriangle α β hα hβ hs).interior =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2)) (Ioo (-Real.cos α) (Real.cos β)) := by
  let U:=prescribedIdealHTriangle α β hα hβ hs
  let T:=U.toDiscTriangle
  let a : ℂ:=⟨-Real.cos α,Real.sin α⟩
  let b : ℂ:=⟨Real.cos β,Real.sin β⟩
  have hab : a.re<b.re:=by
    have h:=angle_pair_cosine_sum_pos α β hα hβ hs
    change -Real.cos α<Real.cos β
    linarith only [h]
  have hc : ‖(T.c:ℂ)‖=1:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff U.c).mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal
  have he:=T.normalized_interior_eq_graph hc 1 (by norm_num)
    (closed_vertex_normalized_identity U.c) ?_
    a b (angle_unit_complex_norm α).1 (angle_unit_complex_norm β).2 hab.ne
    (closed_vertex_normalized_identity U.a) (closed_vertex_normalized_identity U.b) ?_ ?_
  · change T.halfPlaneInterior=_
    simpa only [one_smul,image_id',min_eq_left hab.le,max_eq_right hab.le] using he
  · change ((1:GL (Fin 2) ℝ) • · :ℍ→ℍ) '' U.sideLineC.carrier=_
    rw [prescribedIdealHTriangle_circle]
    simp
  · change ((1:GL (Fin 2) ℝ) • · :ℍ→ℍ) '' U.sideLineA.carrier=_
    rw [prescribedIdealHTriangle_sideA]
    simp [b]
  · change ((1:GL (Fin 2) ℝ) • · :ℍ→ℍ) '' U.sideLineB.carrier=_
    rw [prescribedIdealHTriangle_sideB]
    simp [a]

/-- The relative closed region in H is the genuine weak strip and exterior unit circle,
including every original finite side and every ideal vertex pattern at the boundary. -/
theorem prescribedIdealHTriangle_interior_closure (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) :
    closure (prescribedIdealHTriangle α β hα hβ hs).interior =
      {z:ℍ | z.re∈Icc (-Real.cos α) (Real.cos β) ∧ 1≤‖(z:ℂ)‖^2} := by
  rw [prescribedIdealHTriangle_interior_graph,halfPlane_unitCircleGraph_closure]
  have h:=angle_pair_cosine_sum_pos α β hα hβ hs
  linarith only [h]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The genuine metric comparison with the original vertical mirror is exactly its actual same-side inequality. -/
theorem verticalReflection_dist_compare (c : ℝ) (w z : ℍ) :
    dist z w≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection c w) ↔ 0≤(z.re-c)*(w.re-c) := by
  have hd : 0<2*z.im*w.im:=by positivity
  have hc : dist z w≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection c w) ↔
      Real.cosh (dist z w)≤Real.cosh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection c w)):=
    by rw [Real.cosh_le_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg]
  rw [hc,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_re,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_im,
    div_le_div_iff_of_pos_right hd]
  constructor <;> intro h <;> nlinarith

theorem unitCircleReflection_re (w : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w).re=w.re/(‖(w:ℂ)‖^2) := by
  have he:=congrArg Complex.re (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe 0 1 zero_lt_one w)
  simpa only [Complex.ofReal_zero,Complex.ofReal_one,one_pow,sub_zero,zero_add,
    Complex.div_re,Complex.one_re,Complex.one_im,Complex.conj_re,Complex.conj_im,
    Complex.normSq_conj,one_mul,zero_mul,add_zero,Complex.normSq_eq_norm_sq,Complex.norm_conj,zero_div,UpperHalfPlane.coe_re] using he

theorem unitCircleReflection_im (w : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w).im=w.im/(‖(w:ℂ)‖^2) := by
  have he:=congrArg Complex.im (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe 0 1 zero_lt_one w)
  simpa only [Complex.ofReal_zero,Complex.ofReal_one,one_pow,sub_zero,zero_add,
    Complex.div_im,Complex.one_re,Complex.one_im,Complex.conj_re,Complex.conj_im,
    Complex.normSq_conj,one_mul,zero_mul,zero_sub,neg_neg,Complex.normSq_eq_norm_sq,Complex.norm_conj,zero_div,neg_div,UpperHalfPlane.coe_im] using he

theorem unitCircleReflection_norm_sq (w : ℍ) :
    ‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w:ℂ)‖^2=(‖(w:ℂ)‖^2)⁻¹ := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
  simp


/-- The exact original unit-circle mirror comparison, in the independently fixed native metric. -/
theorem unitCircleReflection_cosh_difference (w z : ℍ) :
    Real.cosh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w))-Real.cosh (dist z w)=
      (‖(z:ℂ)‖^2-1)*(‖(w:ℂ)‖^2-1)/(2*z.im*w.im) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cosh_dist_norm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cosh_dist_norm,unitCircleReflection_re,unitCircleReflection_im,
    unitCircleReflection_norm_sq]
  have hn : ‖(w:ℂ)‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr w.ne_zero)
  have hz : z.im≠0:=z.im_pos.ne'
  have hw : w.im≠0:=w.im_pos.ne'
  have hn0 : ‖(w:ℂ)‖≠0:=norm_ne_zero_iff.mpr w.ne_zero
  field_simp [hn0]
  ring

/-- Weak distance comparison with the actual unit-circle mirror is precisely the true same-side product. -/
theorem unitCircleReflection_dist_compare (w z : ℍ) :
    dist z w≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w) ↔
      0≤(‖(z:ℂ)‖^2-1)*(‖(w:ℂ)‖^2-1) := by
  have hc : dist z w≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w) ↔
      Real.cosh (dist z w)≤Real.cosh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w)):=by
    rw [Real.cosh_le_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg]
  rw [hc,←sub_nonneg,unitCircleReflection_cosh_difference]
  have hd : 0<2*z.im*w.im:=by positivity
  constructor
  · intro h
    have hh:=(le_div_iff₀ hd).mp h
    simpa only [zero_mul] using hh
  · intro h
    apply (le_div_iff₀ hd).mpr
    simpa only [zero_mul] using h

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The open original prescribed triangle has strict genuine strip/circle inequalities. -/
theorem prescribedIdealHTriangle_mem_interior_iff (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) (z : ℍ) :
    z∈(prescribedIdealHTriangle α β hα hβ hs).interior ↔
      z.re∈Ioo (-Real.cos α) (Real.cos β) ∧ 1<‖(z:ℂ)‖^2 := by
  rw [prescribedIdealHTriangle_interior_graph]
  change (z.re∈Ioo (-Real.cos α) (Real.cos β) ∧ Real.sqrt (1-z.re^2)<z.im) ↔ _
  rw [Real.sqrt_lt' z.im_pos,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  change (z.re∈Ioo (-Real.cos α) (Real.cos β) ∧ 1-z.re^2<z.im^2) ↔
    (z.re∈Ioo (-Real.cos α) (Real.cos β) ∧ 1<z.re*z.re+z.im*z.im)
  constructor <;> rintro ⟨hx,hy⟩ <;> exact ⟨hx,by nlinarith⟩

/-- The actual closed Dirichlet inequalities for the three physical mirrors force
membership in the closure of the original ideal triangle. -/
theorem prescribedIdealHTriangle_closedDirichlet_subset (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) (w : ℍ)
    (hw : w∈(prescribedIdealHTriangle α β hα hβ hs).interior) :
    nativeClosedDirichlet (triangleReflectionGroup (prescribedIdealHTriangle α β hα hβ hs)) w ⊆
      closure (prescribedIdealHTriangle α β hα hβ hs).interior := by
  let T:=prescribedIdealHTriangle α β hα hβ hs
  have hmem (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (hL:L∈triangleReflectionSides T) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L∈triangleReflectionGroup T:=
    Subgroup.subset_closure ⟨L,hL,rfl⟩
  have hA:=hmem T.sideLineA (by simp [triangleReflectionSides])
  have hB:=hmem T.sideLineB (by simp [triangleReflectionSides])
  have hC:=hmem T.sideLineC (by simp [triangleReflectionSides])
  rw [prescribedIdealHTriangle_sideA] at hA
  rw [prescribedIdealHTriangle_sideB] at hB
  rw [prescribedIdealHTriangle_circle] at hC
  have hwi:=(prescribedIdealHTriangle_mem_interior_iff α β hα hβ hs w).mp hw
  rw [prescribedIdealHTriangle_interior_closure]
  intro z hz
  have ha:=hz ⟨_,hA⟩
  have hb:=hz ⟨_,hB⟩
  have hc:=hz ⟨_,hC⟩
  change dist z w≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (Real.cos β) w) at ha
  change dist z w≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (-Real.cos α) w) at hb
  change dist z w≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one w) at hc
  rw [verticalReflection_dist_compare] at ha hb
  rw [unitCircleReflection_dist_compare] at hc
  exact ⟨⟨by nlinarith [hwi.1.1],by nlinarith [hwi.1.2]⟩,by nlinarith [hwi.2]⟩

end LowDimensionalTopology.Geometry.Fuchsian
