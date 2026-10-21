module
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The two local sides of a circle

Punctured-circle charts identify connected approaches to a missing point with
intervals approaching one of two endpoints. Consequently three pairwise disjoint
preconnected approaches cannot meet the same missing point, while every
neighborhood contains two such approaches.
-/

@[expose] public section
noncomputable section
open Set Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Two genuine preconnected real sets approaching the same excluded strict
lower endpoint must intersect. -/
theorem real_preconnected_common_lower_endpoint_inter
    {A B : Set ℝ} {a : ℝ} (hA : IsPreconnected A)
    (hAsub : A ⊆ Ioi a) (hBsub : B ⊆ Ioi a)
    (haA : a ∈ closure A) (haB : a ∈ closure B) : (A ∩ B).Nonempty := by
  obtain ⟨x,hx⟩ := (show (closure A).Nonempty from ⟨a,haA⟩).of_closure
  obtain ⟨v,hvx,hvB⟩ := mem_closure_iff.mp haB (Iio x) isOpen_Iio (hAsub hx)
  obtain ⟨u,huv,huA⟩ := mem_closure_iff.mp haA (Iio v) isOpen_Iio (hBsub hvB)
  exact ⟨v,hA.Icc_subset huA hx ⟨huv.le,hvx.le⟩,hvB⟩

/-- The strict upper-endpoint version of the actual real interval argument. -/
theorem real_preconnected_common_upper_endpoint_inter
    {A B : Set ℝ} {b : ℝ} (hA : IsPreconnected A)
    (hAsub : A ⊆ Iio b) (hBsub : B ⊆ Iio b)
    (hbA : b ∈ closure A) (hbB : b ∈ closure B) : (A ∩ B).Nonempty := by
  obtain ⟨x,hx⟩ := (show (closure A).Nonempty from ⟨b,hbA⟩).of_closure
  obtain ⟨v,hxv,hvB⟩ := mem_closure_iff.mp hbB (Ioi x) isOpen_Ioi (hAsub hx)
  obtain ⟨u,hvu,huA⟩ := mem_closure_iff.mp hbA (Ioi v) isOpen_Ioi (hBsub hvB)
  exact ⟨v,hA.Icc_subset hx huA ⟨hxv.le,hvu.le⟩,hvB⟩

/-- Three genuine pairwise disjoint preconnected subsets of an open real
interval cannot all approach one of its two actual endpoints. -/
theorem real_no_triod_interval_endpoints
    (T : Fin 3 → Set ℝ) (a b : ℝ)
    (hpre : ∀ i, IsPreconnected (T i))
    (hsub : ∀ i, T i ⊆ Ioo a b)
    (hend : ∀ i, a ∈ closure (T i) ∨ b ∈ closure (T i))
    (hdis : Pairwise (fun i j => Disjoint (T i) (T j))) : False := by
  have hl (i j : Fin 3) (hij : i ≠ j)
      (hi : a ∈ closure (T i)) (hj : a ∈ closure (T j)) : False := by
    obtain ⟨x,hxi,hxj⟩ := real_preconnected_common_lower_endpoint_inter (hpre i)
      (fun _ hx => (hsub i hx).1) (fun _ hx => (hsub j hx).1) hi hj
    exact disjoint_left.mp (hdis hij) hxi hxj
  have hu (i j : Fin 3) (hij : i ≠ j)
      (hi : b ∈ closure (T i)) (hj : b ∈ closure (T j)) : False := by
    obtain ⟨x,hxi,hxj⟩ := real_preconnected_common_upper_endpoint_inter (hpre i)
      (fun _ hx => (hsub i hx).2) (fun _ hx => (hsub j hx).2) hi hj
    exact disjoint_left.mp (hdis hij) hxi hxj
  rcases hend 0 with h0 | h0 <;> rcases hend 1 with h1 | h1 <;> rcases hend 2 with h2 | h2
  all_goals first
    | exact hl 0 1 (by decide) h0 h1
    | exact hl 0 2 (by decide) h0 h2
    | exact hl 1 2 (by decide) h1 h2
    | exact hu 0 1 (by decide) h0 h1
    | exact hu 0 2 (by decide) h0 h2
    | exact hu 1 2 (by decide) h1 h2

theorem circleNoTriod_arg_lt_pi {u : Circle} (hu : u ≠ Circle.exp Real.pi) :
    Complex.arg (u : ℂ) < Real.pi := by
  apply lt_of_le_of_ne (Complex.arg_le_pi _)
  intro he
  apply hu
  rw [←he]
  exact (Circle.exp_arg u).symm

/-- The genuine argument chart on a circle with its argument cut removed. -/
def circleNoTriod_slitHomeomorph :
    {u : Circle | u ≠ Circle.exp Real.pi} ≃ₜ Ioo (-Real.pi) Real.pi where
  toFun u := ⟨Complex.arg (u.val : ℂ),Complex.neg_pi_lt_arg _,circleNoTriod_arg_lt_pi u.property⟩
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
      ⟨(circleNoTriod_arg_lt_pi u.property).ne,u.val.coe_ne_zero⟩
    have hc : Continuous (fun v : {u : Circle | u ≠ Circle.exp Real.pi} => (v.val : ℂ)) :=
      continuous_subtype_val.comp continuous_subtype_val
    change ContinuousAt (fun v : {u : Circle | u ≠ Circle.exp Real.pi} => Complex.arg (v.val : ℂ)) u
    exact ContinuousAt.comp (f := fun v : {u : Circle | u ≠ Circle.exp Real.pi} => (v.val : ℂ))
      (x := u) (Complex.continuousAt_arg hs) hc.continuousAt
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Circle.exp.continuous.comp continuous_subtype_val

/-- The genuine punctured-circle chart, for an arbitrary omitted point. -/
def circleNoTriod_punctureHomeomorph (a : Circle) :
    {u : Circle | u ≠ a} ≃ₜ Ioo (-Real.pi) Real.pi := by
  let e : Circle ≃ₜ Circle := Homeomorph.mulLeft (Circle.exp Real.pi*a⁻¹)
  have hea : e a = Circle.exp Real.pi := by change Circle.exp Real.pi*a⁻¹*a = _; simp [mul_assoc]
  have hiff (u : Circle) : u ≠ a ↔ e u ≠ Circle.exp Real.pi := by
    rw [←hea,e.injective.ne_iff]
  exact (e.subtype hiff).trans circleNoTriod_slitHomeomorph

/-- The genuine continuous angular parametrization, extended over the two
closed interval ends representing the omitted circle point. -/
def circleNoTriod_angleParam (a : Circle) (t : ℝ) : Circle :=
  a / Circle.exp Real.pi * Circle.exp t

theorem continuous_circleNoTriod_angleParam (a : Circle) : Continuous (circleNoTriod_angleParam a) :=
  continuous_const.mul Circle.exp.continuous

theorem circleNoTriod_punctureHomeomorph_symm_coe (a : Circle) (t : Ioo (-Real.pi) Real.pi) :
    ((circleNoTriod_punctureHomeomorph a).symm t).val = circleNoTriod_angleParam a t.val := by
  change (Circle.exp Real.pi*a⁻¹)⁻¹ * Circle.exp t.val = _
  simp only [mul_inv_rev,inv_inv,circleNoTriod_angleParam,div_eq_mul_inv]

/-- The genuine unit circle has no three pairwise disjoint preconnected arms
approaching the same omitted point. No local arc, manifold, graph or geometric
side structure is assumed. -/
theorem circle_no_three_disjoint_preconnected_approaches
    (u : Circle) (T : Fin 3 → Set Circle)
    (hpre : ∀ i, IsPreconnected (T i))
    (hsub : ∀ i, T i ⊆ {u}ᶜ)
    (hcl : ∀ i, u ∈ closure (T i))
    (hdis : Pairwise (fun i j => Disjoint (T i) (T j))) : False := by
  let e := circleNoTriod_punctureHomeomorph u
  let S : Fin 3 → Set {v : Circle | v ≠ u} := fun i => Subtype.val ⁻¹' T i
  let B : Fin 3 → Set ℝ := fun i => (fun v : {v : Circle | v ≠ u} => (e v).val) '' S i
  let f := circleNoTriod_angleParam u
  have hf : Continuous f := continuous_circleNoTriod_angleParam u
  have hval (i : Fin 3) : (Subtype.val : {v : Circle | v ≠ u} → Circle) '' S i = T i := by
    apply image_preimage_eq_of_subset
    intro v hv
    exact ⟨⟨v,hsub i hv⟩,rfl⟩
  have hBi (i : Fin 3) : IsPreconnected (B i) := by
    have hSi : IsPreconnected (S i) := Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      ((hval i).symm ▸ hpre i)
    exact hSi.image _ (continuous_subtype_val.comp e.continuous).continuousOn
  have hBsub (i : Fin 3) : B i ⊆ Ioo (-Real.pi) Real.pi := by
    rintro t ⟨v,_hv,rfl⟩
    exact (e v).property
  have hrecover (i : Fin 3) : f '' B i = T i := by
    apply subset_antisymm
    · rintro z ⟨t,⟨v,hv,rfl⟩,rfl⟩
      have he : f (e v).val = v.val := by
        change circleNoTriod_angleParam u (e v).val = v.val
        rw [←circleNoTriod_punctureHomeomorph_symm_coe]
        exact congrArg Subtype.val (e.symm_apply_apply v)
      exact he ▸ hv
    · intro v hv
      let w : {v : Circle | v ≠ u} := ⟨v,hsub i hv⟩
      refine ⟨(e w).val,⟨w,hv,rfl⟩,?_⟩
      change circleNoTriod_angleParam u (e w).val = v
      rw [←circleNoTriod_punctureHomeomorph_symm_coe]
      exact congrArg Subtype.val (e.symm_apply_apply w)
  have hend (i : Fin 3) : -Real.pi ∈ closure (B i) ∨ Real.pi ∈ closure (B i) := by
    have hclsub : closure (B i) ⊆ Icc (-Real.pi) Real.pi :=
      closure_minimal ((hBsub i).trans Ioo_subset_Icc_self) isClosed_Icc
    have hc : IsCompact (closure (B i)) := isCompact_Icc.of_isClosed_subset isClosed_closure hclsub
    have hu : u ∈ f '' closure (B i) :=
      closure_minimal ((hrecover i).symm ▸ image_mono subset_closure) (hc.image hf).isClosed (hcl i)
    obtain ⟨t,ht,hft⟩ := hu
    have hte : t = -Real.pi ∨ t = Real.pi := by
      by_contra he
      have htl : -Real.pi < t := lt_of_le_of_ne (hclsub ht).1 (fun h => he (Or.inl h.symm))
      have htr : t < Real.pi := lt_of_le_of_ne (hclsub ht).2 (fun h => he (Or.inr h))
      have hvaleq := circleNoTriod_punctureHomeomorph_symm_coe u ⟨t,htl,htr⟩
      have hne := ((e.symm ⟨t,htl,htr⟩).property)
      exact hne (hvaleq.trans hft)
    rcases hte with rfl | rfl
    · exact Or.inl ht
    · exact Or.inr ht
  have hBdis : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro t hti htj
    exact disjoint_left.mp (hdis hij) ((hrecover i) ▸ mem_image_of_mem f hti)
      ((hrecover j) ▸ mem_image_of_mem f htj)
  exact real_no_triod_interval_endpoints B (-Real.pi) Real.pi hBi hBsub hend hBdis


/-- Every true neighbourhood of an actual circle point contains two genuine
disjoint preconnected approaches to that point, with the point itself deleted. -/
theorem circle_exists_two_preconnected_approaches
    (u : Circle) {U : Set Circle} (hU : U ∈ 𝓝 u) :
    ∃ A B : Set Circle, IsPreconnected A ∧ IsPreconnected B ∧ Disjoint A B ∧
      A ⊆ U \ {u} ∧ B ⊆ U \ {u} ∧ u ∈ closure A ∧ u ∈ closure B := by
  let f : ℝ → Circle := fun t => u * Circle.exp t
  have hfc : Continuous f := continuous_const.mul Circle.exp.continuous
  have hn : f ⁻¹' U ∈ 𝓝 (0:ℝ) := hfc.continuousAt.preimage_mem_nhds
    (by simpa only [f,Circle.exp_zero,mul_one] using hU)
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hn
  let ε := min δ Real.pi / 2
  have hε : 0 < ε := half_pos (lt_min hδ Real.pi_pos)
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ Real.pi]
  have hεπ : ε < Real.pi := by dsimp [ε]; linarith [min_le_right δ Real.pi,Real.pi_pos]
  have hfi : Set.InjOn f (Icc (-ε) ε) := by
    intro s hs t ht he
    apply Circle.exp_injOn_Icc (a := -ε) (b := ε) (by linarith) hs ht
    exact mul_left_cancel he
  have hsub (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (ht0 : t ≠ 0) : f t ∈ U \ {u} := by
    refine ⟨hδU ?_,?_⟩
    · change dist t 0 < δ
      rw [Real.dist_eq,sub_zero]
      exact (abs_lt.mpr ht).trans hεδ
    · intro he
      have heq : f t = u := mem_singleton_iff.mp he
      have he' : f t = f 0 := by simpa only [f,Circle.exp_zero,mul_one] using heq
      exact ht0 (hfi ⟨ht.1.le,ht.2.le⟩ ⟨by linarith,by linarith⟩ he')
  let A := f '' Ioo (0:ℝ) ε
  let B := f '' Ioo (-ε) (0:ℝ)
  refine ⟨A,B,isPreconnected_Ioo.image _ hfc.continuousOn,
    isPreconnected_Ioo.image _ hfc.continuousOn,?_,?_,?_,?_,?_⟩
  · apply disjoint_left.mpr
    rintro z ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
    have hst : s = t := hfi ⟨by linarith [hs.1],hs.2.le⟩
      ⟨ht.1.le,by linarith [ht.2]⟩ he.symm
    linarith [hs.1,ht.2]
  · rintro z ⟨t,ht,rfl⟩
    exact hsub t ⟨by linarith [ht.1],ht.2⟩ (ne_of_gt ht.1)
  · rintro z ⟨t,ht,rfl⟩
    exact hsub t ⟨ht.1,by linarith [ht.2]⟩ (ne_of_lt ht.2)
  · have hm : (0:ℝ) ∈ closure (Ioo (0:ℝ) ε) := by
      rw [closure_Ioo hε.ne]
      exact ⟨le_rfl,hε.le⟩
    simpa only [f,Circle.exp_zero,mul_one] using mem_closure_image hfc.continuousAt hm
  · have hm : (0:ℝ) ∈ closure (Ioo (-ε) (0:ℝ)) := by
      rw [closure_Ioo (by linarith : -ε ≠ (0:ℝ))]
      exact ⟨by linarith,le_rfl⟩
    simpa only [f,Circle.exp_zero,mul_one] using mem_closure_image hfc.continuousAt hm

end LowDimensionalTopology.Geometry.Auxiliary.Topology
