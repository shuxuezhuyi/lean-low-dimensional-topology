/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Euclidean

/-- The actual positive angular period of a primitive finite rotation. -/
def finiteRotationPeriod (n : ℕ) : ℝ:=2*Real.pi/(n:ℝ)

/-- The actual primitive unit complex rotation, acting by literal multiplication. -/
def finiteRotationGenerator (n : ℕ) : Circle:=Circle.exp (finiteRotationPeriod n)

/-- An actual open arc in the genuine complex unit circle. -/
def finiteRotationOpenArc (n : ℕ) : Set Circle:=Circle.exp '' Ioo 0 (finiteRotationPeriod n)

def finiteRotationHalfOpenArc (n : ℕ) : Set Circle:=Circle.exp '' Ico 0 (finiteRotationPeriod n)

def finiteRotationClosedArc (n : ℕ) : Set Circle:=Circle.exp '' Icc 0 (finiteRotationPeriod n)

theorem finiteRotationPeriod_pos (n : ℕ) (hn : 0<n) : 0<finiteRotationPeriod n := by
  exact div_pos (by positivity) (by exact_mod_cast hn)

theorem finiteRotationPeriod_mul (n : ℕ) (hn : n≠0) :
    (n:ℝ)*finiteRotationPeriod n=2*Real.pi := by
  dsimp only [finiteRotationPeriod]
  field_simp

theorem finiteRotationGenerator_isPrimitiveRoot (n : ℕ) (hn : n≠0) :
    IsPrimitiveRoot (finiteRotationGenerator n) n := by
  have hc : IsPrimitiveRoot (Circle.coeHom (finiteRotationGenerator n)) n := by
    change IsPrimitiveRoot (Complex.exp ((finiteRotationPeriod n:ℂ)*Complex.I)) n
    convert Complex.isPrimitiveRoot_exp n hn using 1
    congr 1
    simp only [finiteRotationPeriod,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_ofNat,Complex.ofReal_natCast]
    ring
  exact hc.of_map_of_injective Circle.coe_injective

theorem finiteRotationGenerator_pow (n : ℕ) (hn : n≠0) : finiteRotationGenerator n^n=1 :=
  (finiteRotationGenerator_isPrimitiveRoot n hn).pow_eq_one

/-- Every actual circle point is in a literal rotation of the half-open period arc. -/
theorem finiteRotation_halfOpenArc_cover (n : ℕ) (hn : 0<n) (z : Circle) :
    ∃k : ℤ,∃t∈Ico (0:ℝ) (finiteRotationPeriod n),
      z=finiteRotationGenerator n^k*Circle.exp t := by
  let P:=finiteRotationPeriod n
  have hP : 0<P:=finiteRotationPeriod_pos n hn
  let t:=toIcoMod hP 0 (Complex.arg z)
  let k:=toIcoDiv hP 0 (Complex.arg z)
  refine ⟨k,t,by simpa only [zero_add] using toIcoMod_mem_Ico hP 0 (Complex.arg z),?_⟩
  have hangle : (k:ℝ)*P+t=Complex.arg z := by
    dsimp only [k,t]
    simpa only [zsmul_eq_mul] using toIcoDiv_zsmul_add_toIcoMod hP 0 (Complex.arg z)
  rw [←Circle.exp_arg z]
  change Circle.exp (Complex.arg z)=Circle.exp P^k*Circle.exp t
  rw [←Circle.exp_intCast_mul,←Circle.exp_add]
  exact congrArg Circle.exp hangle.symm

/-- Actual orbit representatives in a single half-open angular period are unique. -/
theorem finiteRotation_halfOpenArc_unique (n : ℕ) (hn : 0<n) (k l : ℤ) (s t : ℝ)
    (hs : s∈Ico (0:ℝ) (finiteRotationPeriod n))
    (ht : t∈Ico (0:ℝ) (finiteRotationPeriod n))
    (he : finiteRotationGenerator n^k*Circle.exp s=finiteRotationGenerator n^l*Circle.exp t) :
    s=t ∧ finiteRotationGenerator n^k=finiteRotationGenerator n^l := by
  let P:=finiteRotationPeriod n
  have hP : 0<P:=finiteRotationPeriod_pos n hn
  have he' : Circle.exp ((k:ℝ)*P+s)=Circle.exp ((l:ℝ)*P+t) := by
    change Circle.exp P^k*Circle.exp s=Circle.exp P^l*Circle.exp t at he
    simpa only [Circle.exp_add,Circle.exp_intCast_mul] using he
  obtain ⟨m,hm⟩:=Circle.exp_eq_exp.mp he'
  let d:=k-l-m*(n:ℤ)
  have hd : (d:ℝ)*P=t-s := by
    have hnP : (n:ℝ)*P=2*Real.pi:=finiteRotationPeriod_mul n hn.ne'
    dsimp only [d]
    push_cast
    linear_combination hm-(m:ℝ)*hnP
  have hdl : (-1:ℝ)<(d:ℝ) := by nlinarith only [hs.1,hs.2,ht.1,ht.2,hd,hP]
  have hdu : (d:ℝ)<1 := by nlinarith only [hs.1,hs.2,ht.1,ht.2,hd,hP]
  have hd0 : d=0 := by
    have hl : (-1:ℤ)<d:=by exact_mod_cast hdl
    have hu : d<(1:ℤ):=by exact_mod_cast hdu
    omega
  have hst : s=t := by rw [hd0,Int.cast_zero,zero_mul] at hd;linarith
  refine ⟨hst,?_⟩
  rw [hst] at he
  exact mul_right_cancel he

/-- Different genuine rotation elements have disjoint actual open period arcs. -/
theorem finiteRotation_openArc_disjoint (n : ℕ) (hn : 0<n) (k l : ℤ)
    (hne : finiteRotationGenerator n^k≠finiteRotationGenerator n^l) :
    Disjoint ((fun z : Circle=>finiteRotationGenerator n^k*z) '' finiteRotationOpenArc n)
      ((fun z : Circle=>finiteRotationGenerator n^l*z) '' finiteRotationOpenArc n) := by
  apply disjoint_left.mpr
  rintro z ⟨_,⟨s,hs,rfl⟩,rfl⟩ ⟨_,⟨t,ht,rfl⟩,he⟩
  exact hne (finiteRotation_halfOpenArc_unique n hn k l s t
    ⟨hs.1.le,hs.2⟩ ⟨ht.1.le,ht.2⟩ he.symm).2

/-- The sector arc is genuinely open in the original unit-circle topology. -/
theorem finiteRotationOpenArc_isOpen (n : ℕ) : IsOpen (finiteRotationOpenArc n) :=
  Circle.isCoveringMap_exp.isOpenMap _ isOpen_Ioo

/-- The genuine topological closure includes exactly the two expected boundary rays. -/
theorem finiteRotationOpenArc_closure (n : ℕ) (hn : 0<n) :
    closure (finiteRotationOpenArc n)=finiteRotationClosedArc n := by
  have hP:=finiteRotationPeriod_pos n hn
  have hc : IsClosed (finiteRotationClosedArc n):=
    (isCompact_Icc.image Circle.exp.continuous).isClosed
  apply subset_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self) hc
  · have h:=image_closure_subset_closure_image (s:=Ioo (0:ℝ) (finiteRotationPeriod n)) Circle.exp.continuous
    rw [closure_Ioo hP.ne] at h
    exact h

/-- Every integral power is one of the actual n finite rotation elements. -/
theorem finiteRotationGenerator_zpow_eq_fin (n : ℕ) (hn : 0<n) (k : ℤ) :
    ∃i : Fin n,finiteRotationGenerator n^k=finiteRotationGenerator n^i.val := by
  let j:=k%(n:ℤ)
  have hj0 : 0≤j:=Int.emod_nonneg k (by exact_mod_cast hn.ne')
  have hjn : j<(n:ℤ):=Int.emod_lt_of_pos k (by exact_mod_cast hn)
  let i : Fin n:=⟨j.toNat,by
    have hi : (j.toNat:ℤ)<(n:ℤ):=by rw [Int.toNat_of_nonneg hj0];exact hjn
    exact_mod_cast hi⟩
  refine ⟨i,?_⟩
  calc finiteRotationGenerator n^k=finiteRotationGenerator n^j:=
         zpow_eq_zpow_emod' k (finiteRotationGenerator_pow n hn.ne')
       _=finiteRotationGenerator n^(i.val:ℤ):=by
         congr 1
         exact (Int.toNat_of_nonneg hj0).symm
       _=finiteRotationGenerator n^i.val:=zpow_natCast _ _

/-- The original circle is covered by the actual finitely many closed angular sectors. -/
theorem finiteRotation_closedArc_finite_cover (n : ℕ) (hn : 0<n) :
    (⋃i : Fin n,(fun z : Circle=>finiteRotationGenerator n^i.val*z) '' finiteRotationClosedArc n)=univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨k,t,ht,hz⟩:=finiteRotation_halfOpenArc_cover n hn z
  obtain ⟨i,hi⟩:=finiteRotationGenerator_zpow_eq_fin n hn k
  exact mem_iUnion.mpr ⟨i,Circle.exp t,⟨t,⟨ht.1,ht.2.le⟩,rfl⟩,by rw [←hi];exact hz.symm⟩

/-- The genuine finite rotation elements are distinct, not merely distinct indices. -/
theorem finiteRotationGenerator_pow_fin_injective (n : ℕ) (hn : 0<n) :
    Function.Injective (fun i : Fin n=>finiteRotationGenerator n^i.val) := by
  intro i j he
  exact Fin.ext ((finiteRotationGenerator_isPrimitiveRoot n hn.ne').pow_inj i.isLt j.isLt he)

/-- The actual n open angular sectors are pairwise disjoint in the original circle. -/
theorem finiteRotation_openArc_finite_disjoint (n : ℕ) (hn : 0<n) :
    Pairwise (fun i j : Fin n=>Disjoint
      ((fun z : Circle=>finiteRotationGenerator n^i.val*z) '' finiteRotationOpenArc n)
      ((fun z : Circle=>finiteRotationGenerator n^j.val*z) '' finiteRotationOpenArc n)) := by
  intro i j hne
  have hpow : finiteRotationGenerator n^(i.val:ℤ)≠finiteRotationGenerator n^(j.val:ℤ) := by
    simpa only [zpow_natCast] using (finiteRotationGenerator_pow_fin_injective n hn).ne hne
  simpa only [zpow_natCast] using finiteRotation_openArc_disjoint n hn (i.val:ℤ) (j.val:ℤ) hpow

/-- The actual direction of a nonzero complex number in the original unit circle. -/
def finiteSectorDirection (z : {z : ℂ // z ≠ 0}) : Circle :=
  ⟨z.val / (‖z.val‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact div_self (norm_ne_zero_iff.mpr z.property)⟩

theorem finiteSectorDirection_continuous : Continuous finiteSectorDirection := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.div
    (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
    (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.property))

theorem finiteSectorDirection_reconstruct (z : {z : ℂ // z ≠ 0}) :
    (‖z.val‖ : ℂ) * (finiteSectorDirection z : ℂ) = z.val := by
  change (‖z.val‖ : ℂ) * (z.val / (‖z.val‖ : ℂ)) = z.val
  field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.property)]

theorem finiteSectorDirection_radial (r : ℝ) (hr : 0<r) (u : Circle) :
    finiteSectorDirection ⟨(r:ℂ)*(u:ℂ),mul_ne_zero
      (Complex.ofReal_ne_zero.mpr hr.ne') u.coe_ne_zero⟩ = u := by
  apply Circle.ext
  change ((r:ℂ)*(u:ℂ)) / (‖(r:ℂ)*(u:ℂ)‖ : ℂ) = (u:ℂ)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,Circle.norm_coe,mul_one]
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne']

theorem finiteSectorDirection_rotation (u : Circle) (z : {z : ℂ // z ≠ 0}) :
    finiteSectorDirection ⟨(u:ℂ)*z.val,mul_ne_zero u.coe_ne_zero z.property⟩ =
      u * finiteSectorDirection z := by
  apply Circle.ext
  change ((u:ℂ)*z.val)/(‖(u:ℂ)*z.val‖:ℂ) =
    (u:ℂ)*(z.val/(‖z.val‖:ℂ))
  rw [norm_mul,Circle.norm_coe,one_mul]
  ring

/-- The genuine open planar sector; the origin is excluded. -/
def finiteRotationPlaneSector (n : ℕ) : Set ℂ :=
  Subtype.val '' (finiteSectorDirection ⁻¹' finiteRotationOpenArc n)

theorem finiteRotationPlaneSector_isOpen (n : ℕ) : IsOpen (finiteRotationPlaneSector n) := by
  exact (isOpen_ne_fun continuous_id continuous_const).isOpenMap_subtype_val _
    ((finiteRotationOpenArc_isOpen n).preimage finiteSectorDirection_continuous)

theorem finiteRotationPlaneSector_mem_iff (n : ℕ) (z : ℂ) :
    z∈finiteRotationPlaneSector n ↔
      ∃r : ℝ,0<r ∧ ∃t∈Ioo (0:ℝ) (finiteRotationPeriod n),
        z=(r:ℂ)*(Circle.exp t:ℂ) := by
  constructor
  · rintro ⟨w,⟨t,ht,he⟩,rfl⟩
    refine ⟨‖w.val‖,norm_pos_iff.mpr w.property,t,ht,?_⟩
    rw [he]
    exact (finiteSectorDirection_reconstruct w).symm
  · rintro ⟨r,hr,t,ht,rfl⟩
    let w : {z : ℂ // z≠0}:=⟨(r:ℂ)*(Circle.exp t:ℂ),
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Circle.exp t).coe_ne_zero⟩
    refine ⟨w,?_,rfl⟩
    change finiteSectorDirection w ∈ finiteRotationOpenArc n
    rw [finiteSectorDirection_radial r hr (Circle.exp t)]
    exact ⟨t,ht,rfl⟩

/-- The genuine closed cone over the closed fundamental arc, including its vertex. -/
def finiteRotationClosedPlaneSector (n : ℕ) : Set ℂ :=
  insert 0 (Subtype.val '' (finiteSectorDirection ⁻¹' finiteRotationClosedArc n))

theorem finiteRotationClosedPlaneSector_isClosed (n : ℕ) :
    IsClosed (finiteRotationClosedPlaneSector n) := by
  have hc : IsClosed (finiteRotationClosedArc n) :=
    (isCompact_Icc.image Circle.exp.continuous).isClosed
  have he : (finiteRotationClosedPlaneSector n)ᶜ =
      Subtype.val '' (finiteSectorDirection ⁻¹' (finiteRotationClosedArc n)ᶜ) := by
    ext z
    constructor
    · intro hz
      have hz0 : z≠0 := fun h => hz (Or.inl h)
      refine ⟨⟨z,hz0⟩,?_,rfl⟩
      exact fun h => hz (Or.inr ⟨⟨z,hz0⟩,h,rfl⟩)
    · rintro ⟨w,hw,rfl⟩ (h0|⟨v,hv,heq⟩)
      · exact w.property h0
      · have heq' : v=w := Subtype.ext heq
        exact hw (heq' ▸ hv)
  rw [←isOpen_compl_iff,he]
  exact (isOpen_ne_fun continuous_id continuous_const).isOpenMap_subtype_val _
    (hc.isOpen_compl.preimage finiteSectorDirection_continuous)

theorem finiteRotationClosedPlaneSector_radial (n : ℕ) (r : ℝ) (hr : 0<r)
    (u : Circle) (hu : u∈finiteRotationClosedArc n) :
    (r:ℂ)*(u:ℂ) ∈ finiteRotationClosedPlaneSector n := by
  right
  refine ⟨⟨(r:ℂ)*(u:ℂ),mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') u.coe_ne_zero⟩,?_,rfl⟩
  change finiteSectorDirection _ ∈ finiteRotationClosedArc n
  simpa only [finiteSectorDirection_radial r hr u] using hu

/-- Closing the actual open planar sector adds exactly its two rays and vertex. -/
theorem finiteRotationPlaneSector_closure (n : ℕ) (hn : 0<n) :
    closure (finiteRotationPlaneSector n)=finiteRotationClosedPlaneSector n := by
  have hP:=finiteRotationPeriod_pos n hn
  apply subset_antisymm
  · apply closure_minimal _ (finiteRotationClosedPlaneSector_isClosed n)
    rintro _ ⟨w,hw,rfl⟩
    exact Or.inr ⟨w,image_mono Ioo_subset_Icc_self hw,rfl⟩
  · rintro z (rfl|⟨w,hw,rfl⟩)
    · let u:=Circle.exp (finiteRotationPeriod n/2)
      have hu : u∈finiteRotationOpenArc n:=⟨finiteRotationPeriod n/2,by constructor <;> linarith,rfl⟩
      have hf : Continuous (fun r : ℝ=>(r:ℂ)*(u:ℂ)):=by fun_prop
      have hi:=image_closure_subset_closure_image (s:=Ioi (0:ℝ)) hf
      have h0 : (0:ℂ)∈(fun r : ℝ=>(r:ℂ)*(u:ℂ)) '' closure (Ioi (0:ℝ)):=by
        refine ⟨0,by simp [closure_Ioi],by simp⟩
      apply (closure_mono (t:=finiteRotationPlaneSector n) ?_) (hi h0)
      rintro _ ⟨r,hr,rfl⟩
      refine ⟨⟨(r:ℂ)*(u:ℂ),mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') u.coe_ne_zero⟩,?_,rfl⟩
      change finiteSectorDirection _ ∈ finiteRotationOpenArc n
      simpa only [finiteSectorDirection_radial r hr u] using hu
    · let r:=‖w.val‖
      have hr : 0<r:=norm_pos_iff.mpr w.property
      have hf : Continuous (fun u : Circle=>(r:ℂ)*(u:ℂ)):=by fun_prop
      have hi:=image_closure_subset_closure_image (s:=finiteRotationOpenArc n) hf
      have hz : w.val∈(fun u : Circle=>(r:ℂ)*(u:ℂ)) '' closure (finiteRotationOpenArc n):=by
        refine ⟨finiteSectorDirection w,?_,finiteSectorDirection_reconstruct w⟩
        rwa [finiteRotationOpenArc_closure n hn]
      apply (closure_mono (t:=finiteRotationPlaneSector n) ?_) (hi hz)
      rintro _ ⟨u,hu,rfl⟩
      refine ⟨⟨(r:ℂ)*(u:ℂ),mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') u.coe_ne_zero⟩,?_,rfl⟩
      change finiteSectorDirection _ ∈ finiteRotationOpenArc n
      simpa only [finiteSectorDirection_radial r hr u] using hu

/-- Literal complex rotations of the closed planar sector cover the whole plane. -/
theorem finiteRotation_closedPlaneSector_finite_cover (n : ℕ) (hn : 0<n) :
    (⋃i : Fin n,(fun z : ℂ=>(finiteRotationGenerator n^i.val:Circle)*z) ''
      finiteRotationClosedPlaneSector n)=univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : z=0
  · subst z
    exact mem_iUnion.mpr ⟨⟨0,hn⟩,0,Or.inl rfl,by simp⟩
  · let w : {z : ℂ // z≠0}:=⟨z,hz⟩
    have hu : finiteSectorDirection w∈⋃i : Fin n,
        (fun u : Circle=>finiteRotationGenerator n^i.val*u) '' finiteRotationClosedArc n:=by
      rw [finiteRotation_closedArc_finite_cover n hn]
      trivial
    obtain ⟨i,u,hu,he⟩:=mem_iUnion.mp hu
    refine mem_iUnion.mpr ⟨i,(‖z‖:ℂ)*(u:ℂ),
      finiteRotationClosedPlaneSector_radial n ‖z‖ (norm_pos_iff.mpr hz) u hu,?_⟩
    calc
      (finiteRotationGenerator n^i.val:Circle)*((‖z‖:ℂ)*(u:ℂ))=
          (‖z‖:ℂ)*((finiteRotationGenerator n^i.val:Circle)*(u:ℂ)):=by ring
      _=(‖z‖:ℂ)*(finiteSectorDirection w:ℂ):=
        congrArg (fun v : Circle=>(‖z‖:ℂ)*(v:ℂ)) he
      _=z:=finiteSectorDirection_reconstruct w

/-- Actual rotated open planar sectors have disjoint interiors. -/
theorem finiteRotation_openPlaneSector_finite_disjoint (n : ℕ) (hn : 0<n) :
    Pairwise (fun i j : Fin n=>Disjoint
      ((fun z : ℂ=>(finiteRotationGenerator n^i.val:Circle)*z) '' finiteRotationPlaneSector n)
      ((fun z : ℂ=>(finiteRotationGenerator n^j.val:Circle)*z) '' finiteRotationPlaneSector n)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro z ⟨y,⟨v,hv,rfl⟩,hy⟩ ⟨x,⟨w,hw,rfl⟩,hx⟩
  have he : finiteRotationGenerator n^i.val*finiteSectorDirection v=
      finiteRotationGenerator n^j.val*finiteSectorDirection w:=by
    rw [←finiteSectorDirection_rotation,←finiteSectorDirection_rotation]
    exact congrArg finiteSectorDirection (Subtype.ext (hy.trans hx.symm))
  exact disjoint_left.mp (finiteRotation_openArc_finite_disjoint n hn hij)
    ⟨finiteSectorDirection v,hv,rfl⟩ ⟨finiteSectorDirection w,hw,he.symm⟩

/-- The same genuine finite rotations tile every genuine centred Euclidean ball. -/
theorem finiteRotation_closedPlaneSector_ball_cover (n : ℕ) (hn : 0<n) (R : ℝ) :
    (⋃i : Fin n,(fun z : ℂ=>(finiteRotationGenerator n^i.val:Circle)*z) ''
      (finiteRotationClosedPlaneSector n∩Metric.ball 0 R))=Metric.ball 0 R := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,w,⟨_,hw⟩,rfl⟩:=mem_iUnion.mp hz
    simpa only [Metric.mem_ball,dist_zero_right,norm_mul,Circle.norm_coe,one_mul] using hw
  · intro hz
    have hu : z∈⋃i : Fin n,(fun w : ℂ=>(finiteRotationGenerator n^i.val:Circle)*w) ''
        finiteRotationClosedPlaneSector n:=by rw [finiteRotation_closedPlaneSector_finite_cover n hn];trivial
    obtain ⟨i,w,hw,rfl⟩:=mem_iUnion.mp hu
    refine mem_iUnion.mpr ⟨i,w,⟨hw,?_⟩,rfl⟩
    simpa only [Metric.mem_ball,dist_zero_right,norm_mul,Circle.norm_coe,one_mul] using hz

end LowDimensionalTopology.Geometry.Euclidean
