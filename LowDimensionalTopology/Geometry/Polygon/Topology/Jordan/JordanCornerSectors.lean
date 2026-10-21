module
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanPolygonRegions
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteRotationSectors
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CircleNoTriod
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.RadialLocalAngularMeasure
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon

/-- Two genuinely connected local complementary pieces must select different
sides of two open complementary regions having the same actual frontier. -/
theorem two_frontier_regions_local_partition
    {X : Type*} [TopologicalSpace X] {I O C U A B : Set X} {x : X}
    (hI : IsOpen I) (hO : IsOpen O) (hdis : Disjoint I O)
    (hcover : (I∪O)∩U=U\C) (hxI : x∈frontier I) (hxO : x∈frontier O)
    (hU : U∈𝓝 x) (hAB : A∪B=U\C)
    (hA : IsPreconnected A) (hB : IsPreconnected B) :
    I∩U=A ∨ I∩U=B := by
  have hsub : A∪B⊆I∪O := by
    intro y hy
    have hyUC : y∈U\C:=hAB ▸ hy
    exact (show y∈(I∪O)∩U from hcover.symm ▸ hyUC).1
  have ha:=IsPreconnected.subset_or_subset hI hO hdis (subset_union_left.trans hsub) hA
  have hb:=IsPreconnected.subset_or_subset hI hO hdis (subset_union_right.trans hsub) hB
  have htouchI : (U∩I).Nonempty:=mem_closure_iff_nhds.mp (frontier_subset_closure hxI) U hU
  have htouchO : (U∩O).Nonempty:=mem_closure_iff_nhds.mp (frontier_subset_closure hxO) U hU
  have hiC : ∀y∈U,y∈I→y∉C := by
    intro y hyU hyI
    exact (show y∈U\C from hcover ▸ (show y∈(I∪O)∩U from ⟨Or.inl hyI,hyU⟩)).2
  have hoC : ∀y∈U,y∈O→y∉C := by
    intro y hyU hyO
    exact (show y∈U\C from hcover ▸ (show y∈(I∪O)∩U from ⟨Or.inr hyO,hyU⟩)).2
  have hsameI : ¬(A⊆I ∧ B⊆I) := by
    rintro ⟨ha,hb⟩
    obtain ⟨y,hyU,hyO⟩ := htouchO
    have hyAB : y∈A∪B:=hAB.symm ▸ ⟨hyU,hoC y hyU hyO⟩
    exact disjoint_left.mp hdis ((union_subset ha hb) hyAB) hyO
  have hsameO : ¬(A⊆O ∧ B⊆O) := by
    rintro ⟨ha,hb⟩
    obtain ⟨y,hyU,hyI⟩ := htouchI
    have hyAB : y∈A∪B:=hAB.symm ▸ ⟨hyU,hiC y hyU hyI⟩
    exact disjoint_left.mp hdis hyI ((union_subset ha hb) hyAB)
  have heq {S T : Set X} (hST : S∪T=U\C) (hSI : S⊆I) (hTO : T⊆O) : I∩U=S := by
    ext y
    constructor
    · rintro ⟨hyI,hyU⟩
      have hyST : y∈S∪T:=hST.symm ▸ ⟨hyU,hiC y hyU hyI⟩
      exact hyST.resolve_right (fun hyT=>disjoint_left.mp hdis hyI (hTO hyT))
    · intro hyS
      exact ⟨hSI hyS,(hST ▸ (show y∈S∪T from Or.inl hyS)).1⟩
  rcases ha with ha|ha <;> rcases hb with hb|hb
  · exact False.elim (hsameI ⟨ha,hb⟩)
  · exact Or.inl (heq hAB ha hb)
  · exact Or.inr (heq (by rw [union_comm,hAB]) hb ha)
  · exact False.elim (hsameO ⟨ha,hb⟩)

/-- The actual bounded Jordan region selects one of the two genuinely
connected local complementary pieces, without a convexity assumption. -/
theorem complexJordan_local_partition {C U A B : Set ℂ} (hC : IsComplexJordanCurve C)
    (h0 : (0:ℂ)∈C) (hU : U∈𝓝 (0:ℂ)) (hAB : A∪B=U\C)
    (hA : IsPreconnected A) (hB : IsPreconnected B) :
    complexJordanInside C∩U=A ∨ complexJordanInside C∩U=B := by
  obtain ⟨hI,hO,hd,hcover,_hIc,_hOc,hFI,hFO⟩ := complexJordan_regions hC
  have hlocal : (complexJordanInside C∪complexJordanOutside C)∩U=U\C := by
    rw [hcover]
    ext y
    simp only [mem_inter_iff,mem_compl_iff,Set.mem_sdiff]
    tauto
  apply two_frontier_regions_local_partition hI hO hd hlocal
    (hFI.symm ▸ h0) (hFO.symm ▸ h0) hU hAB hA hB


/-- A literal full-period open angular interval is exactly a punctured circle. -/
theorem circle_exp_open_period (a : ℝ) :
    Circle.exp '' Ioo a (a+2*Real.pi)={u : Circle | u≠Circle.exp a} := by
  have hfull : Circle.exp '' Ico a (a+2*Real.pi)=univ := by
    have hh:=congrArg (fun S : Set (AddCircle (2*Real.pi))=>AddCircle.homeomorphCircle' '' S)
      (AddCircle.coe_image_Ico_eq (2*Real.pi) a)
    simpa only [image_image,AddCircle.homeomorphCircle'_apply_mk,image_univ,
      AddCircle.homeomorphCircle'.surjective.range_eq] using hh
  have hinj:=Circle.exp_injOn_Ico (a:=a) (b:=a+2*Real.pi) (by linarith)
  ext u
  constructor
  · rintro ⟨t,ht,rfl⟩ he
    have hh:=hinj ⟨ht.1.le,ht.2⟩ ⟨le_rfl,by linarith [Real.pi_pos]⟩ he
    exact ht.1.ne' hh
  · intro hu
    obtain ⟨t,ht,rfl⟩ := hfull.symm ▸ (mem_univ u)
    refine ⟨t,⟨lt_of_le_of_ne ht.1 ?_,ht.2⟩,rfl⟩
    exact fun he=>hu (congrArg Circle.exp he.symm)

/-- Two distinct actual directions admit genuine increasing angular lifts
within one period, including the straight and reflex cases. -/
theorem circle_distinct_ordered_lifts (u v : Circle) (hne : u≠v) :
    ∃a b : ℝ,a<b ∧ b<a+2*Real.pi ∧ Circle.exp a=u ∧ Circle.exp b=v := by
  let a:=Complex.arg (u:ℂ)
  have hu : Circle.exp a=u:=Circle.exp_arg u
  have hv : v∈Circle.exp '' Ioo a (a+2*Real.pi) := by
    rw [circle_exp_open_period]
    change v≠Circle.exp a
    rw [hu]
    exact hne.symm
  obtain ⟨b,hb,hbv⟩ := hv
  exact ⟨a,b,hb.1,hb.2,hu,hbv⟩

/-- The two genuine complementary open arcs cover precisely the circle
with both true endpoint directions removed, and are literally disjoint. -/
theorem circle_exp_two_arcs_partition (a b : ℝ) (hab : a<b) (hba : b<a+2*Real.pi) :
    (Circle.exp '' Ioo a b)∪(Circle.exp '' Ioo b (a+2*Real.pi))=
      {u : Circle | u≠Circle.exp a ∧ u≠Circle.exp b} ∧
    Disjoint (Circle.exp '' Ioo a b) (Circle.exp '' Ioo b (a+2*Real.pi)) := by
  have hinj:=Circle.exp_injOn_Ico (a:=a) (b:=a+2*Real.pi) (by linarith)
  constructor
  · ext u
    constructor
    · rintro (⟨t,ht,rfl⟩|⟨t,ht,rfl⟩)
      · constructor
        · intro he
          exact ht.1.ne' (hinj ⟨ht.1.le,ht.2.trans hba⟩ ⟨le_rfl,by linarith [Real.pi_pos]⟩ he)
        · intro he
          exact ht.2.ne (hinj ⟨ht.1.le,ht.2.trans hba⟩ ⟨hab.le,hba⟩ he)
      · constructor
        · intro he
          exact (hab.trans ht.1).ne' (hinj ⟨(hab.trans ht.1).le,ht.2⟩ ⟨le_rfl,by linarith [Real.pi_pos]⟩ he)
        · intro he
          exact ht.1.ne' (hinj ⟨(hab.trans ht.1).le,ht.2⟩ ⟨hab.le,hba⟩ he)
    · rintro ⟨hua,hub⟩
      have hu' : u∈Circle.exp '' Ioo a (a+2*Real.pi) := by
        rw [circle_exp_open_period]
        exact hua
      obtain ⟨t,ht,rfl⟩ := hu'
      have htb : t≠b:=fun he=>hub (congrArg Circle.exp he)
      rcases lt_or_gt_of_ne htb with h|h
      · exact Or.inl ⟨t,⟨ht.1,h⟩,rfl⟩
      · exact Or.inr ⟨t,⟨h,ht.2⟩,rfl⟩
  · apply disjoint_left.mpr
    rintro u ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
    have hst:=hinj ⟨(hab.trans ht.1).le,ht.2⟩ ⟨hs.1.le,hs.2.trans hba⟩ he
    linarith [hs.2,ht.1]


/-- A literal small open radial sector, using actual complex multiplication
and an ordinary real angular interval, including reflex angular widths. -/
def cornerOpenRadialSector (a b ε : ℝ) : Set ℂ:=
  (fun p : ℝ × ℝ=>(p.1:ℂ)*(Circle.exp p.2:ℂ)) '' (Ioo (0:ℝ) ε ×ˢ Ioo a b)

/-- The genuine radial angular parametrization is continuous on the whole
parameter plane; no local branch of argument is assumed. -/
theorem continuous_corner_radial_param :
    Continuous (fun p : ℝ × ℝ=>(p.1:ℂ)*(Circle.exp p.2:ℂ)) :=
  (Complex.continuous_ofReal.comp continuous_fst).mul
    (continuous_subtype_val.comp (Circle.exp.continuous.comp continuous_snd))

/-- Actual open radial sectors are preconnected, even when their angle
exceeds pi. -/
theorem cornerOpenRadialSector_preconnected (a b ε : ℝ) :
    IsPreconnected (cornerOpenRadialSector a b ε) :=
  (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ continuous_corner_radial_param.continuousOn

/-- The true closure of a bounded open radial sector is the image of the
closed radial/angular rectangle, with the actual origin included. -/
theorem cornerOpenRadialSector_closure (a b ε : ℝ) (hab : a<b) (hε : 0<ε) :
    closure (cornerOpenRadialSector a b ε)=
      (fun p : ℝ × ℝ=>(p.1:ℂ)*(Circle.exp p.2:ℂ)) '' (Icc (0:ℝ) ε ×ˢ Icc a b) := by
  have hc:=continuous_corner_radial_param
  apply subset_antisymm
  · apply closure_minimal (image_mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
    exact ((isCompact_Icc.prod isCompact_Icc).image hc).isClosed
  · have hh:=image_closure_subset_closure_image (s:=Ioo (0:ℝ) ε ×ˢ Ioo a b) hc
    rw [closure_prod_eq,closure_Ioo hε.ne,closure_Ioo hab.ne] at hh
    exact hh

/-- The existing actual closed direction arc is exactly the exponential
image of its real centered interval, for every radius. -/
theorem polygonClosedDirectionArc_eq_exp_Icc (a r : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc (a:AddCircle (2*Real.pi)) r=Circle.exp '' Icc (a-r) (a+r) := by
  ext u
  constructor
  · rintro ⟨q,hq,hqu⟩
    obtain ⟨x⟩ := q
    have hx : x∈((↑) : ℝ→AddCircle (2*Real.pi)) ⁻¹' Metric.closedBall (a:AddCircle (2*Real.pi)) r:=hq
    rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    have hn' : |x-(a+(n:ℝ)*(2*Real.pi))|≤r := by
      simpa only [Metric.mem_closedBall,Real.dist_eq,zsmul_eq_mul] using hn
    refine ⟨x-(n:ℝ)*(2*Real.pi),?_,?_⟩
    · obtain ⟨hl,hr⟩ := abs_le.mp hn'
      constructor <;> linarith
    · rw [Circle.exp_sub,Circle.exp_int_mul_two_pi,div_one]
      exact hqu
  · rintro ⟨t,ht,rfl⟩
    refine ⟨(t:AddCircle (2*Real.pi)),?_,rfl⟩
    change t∈((↑) : ℝ→AddCircle (2*Real.pi)) ⁻¹' Metric.closedBall (a:AddCircle (2*Real.pi)) r
    rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
    apply mem_iUnion.mpr
    refine ⟨0,?_⟩
    simp only [zero_zsmul,add_zero,Metric.mem_closedBall,Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩


/-- The literal nonnegative Euclidean ray with genuine unit direction. -/
def cornerNonnegativeRay (u : Circle) : Set ℂ:={z | ∃t : ℝ,0≤t ∧ z=(t:ℂ)*(u:ℂ)}

theorem corner_positive_radial_mem_ray (r : ℝ) (hr : 0<r) (u v : Circle) :
    (r:ℂ)*(u:ℂ)∈cornerNonnegativeRay v ↔ u=v := by
  constructor
  · rintro ⟨t,ht,he⟩
    have hrt : r=t := by
      have hh:=congrArg norm he
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
        abs_of_nonneg ht,Circle.norm_coe,mul_one] using hh
    rw [←hrt] at he
    exact Circle.coe_injective (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') he)
  · rintro rfl
    exact ⟨r,hr.le,rfl⟩

/-- Every point of the two actual small complementary sectors is in the
punctured ball with both literal boundary rays removed, and conversely. -/
theorem cornerOpenRadialSector_two_partition (a b ε : ℝ) (hab : a<b)
    (hba : b<a+2*Real.pi) :
    cornerOpenRadialSector a b ε∪cornerOpenRadialSector b (a+2*Real.pi) ε=
      Metric.ball (0:ℂ) ε\(cornerNonnegativeRay (Circle.exp a)∪cornerNonnegativeRay (Circle.exp b)) := by
  have harcs:=(circle_exp_two_arcs_partition a b hab hba).1
  have hpos (r : ℝ) (hr : 0<r) (t : ℝ) : ‖(r:ℂ)*(Circle.exp t:ℂ)‖=r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,Circle.norm_coe,mul_one]
  have hd (t : ℝ) (ht : Circle.exp t∈Circle.exp '' Ioo a b∪Circle.exp '' Ioo b (a+2*Real.pi)) :
      Circle.exp t≠Circle.exp a ∧ Circle.exp t≠Circle.exp b := by
    have hh : Circle.exp t∈{u : Circle | u≠Circle.exp a ∧u≠Circle.exp b}:=harcs ▸ ht
    exact hh
  ext z
  constructor
  · rintro (⟨⟨r,t⟩,⟨hr,ht⟩,rfl⟩|⟨⟨r,t⟩,⟨hr,ht⟩,rfl⟩)
    · refine ⟨?_,?_⟩
      · simpa only [Metric.mem_ball,dist_zero_right,hpos r hr.1 t] using hr.2
      · have hdir:=hd t (Or.inl ⟨t,ht,rfl⟩)
        exact fun h=>h.elim (fun h=>hdir.1 ((corner_positive_radial_mem_ray r hr.1 _ _).mp h))
          (fun h=>hdir.2 ((corner_positive_radial_mem_ray r hr.1 _ _).mp h))
    · refine ⟨?_,?_⟩
      · simpa only [Metric.mem_ball,dist_zero_right,hpos r hr.1 t] using hr.2
      · have hdir:=hd t (Or.inr ⟨t,ht,rfl⟩)
        exact fun h=>h.elim (fun h=>hdir.1 ((corner_positive_radial_mem_ray r hr.1 _ _).mp h))
          (fun h=>hdir.2 ((corner_positive_radial_mem_ray r hr.1 _ _).mp h))
  · rintro ⟨hzε,hzR⟩
    have hz0 : z≠0 := by
      rintro rfl
      exact hzR (Or.inl ⟨0,le_rfl,by simp⟩)
    let u:=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨z,hz0⟩
    have hr : 0<‖z‖:=norm_pos_iff.mpr hz0
    have hnorm : ‖z‖<ε:=by simpa only [Metric.mem_ball,dist_zero_right] using hzε
    have hrecon : (‖z‖:ℂ)*(u:ℂ)=z:=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_reconstruct ⟨z,hz0⟩
    have hu : u∈Circle.exp '' Ioo a b∪Circle.exp '' Ioo b (a+2*Real.pi) := by
      rw [harcs]
      constructor
      · intro he
        apply hzR
        exact Or.inl ⟨‖z‖,hr.le,by rw [←he];exact hrecon.symm⟩
      · intro he
        apply hzR
        exact Or.inr ⟨‖z‖,hr.le,by rw [←he];exact hrecon.symm⟩
    rcases hu with ⟨t,ht,htu⟩|⟨t,ht,htu⟩
    · exact Or.inl ⟨(‖z‖,t),⟨⟨hr,hnorm⟩,ht⟩,by change (‖z‖:ℂ)*(Circle.exp t:ℂ)=z;rw [htu];exact hrecon⟩
    · exact Or.inr ⟨(‖z‖,t),⟨⟨hr,hnorm⟩,ht⟩,by change (‖z‖:ℂ)*(Circle.exp t:ℂ)=z;rw [htu];exact hrecon⟩

/-- The actual closure of either small radial piece, viewed in the original
disc, has exactly the prescribed closed angular-sector germ. -/
theorem cornerOpenRadialSector_closure_disc_germ (a b ε : ℝ)
    (hab : a<b) (hε : 0<ε) :
    ∀ᶠ (z : 𝔻) in 𝓝 (0:𝔻),
      (z:ℂ)∈closure (cornerOpenRadialSector a b ε) ↔
      z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector ((((a+b)/2:ℝ):AddCircle (2*Real.pi))) ((b-a)/2) := by
  have hA : _root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc ((((a+b)/2:ℝ):AddCircle
    (2*Real.pi))) ((b-a)/2)=
      Circle.exp '' Icc a b := by
    rw [polygonClosedDirectionArc_eq_exp_Icc]
    congr 2 <;> ring
  have hN : {z : 𝔻 | ‖(z:ℂ)‖<ε}∈𝓝 (0:𝔻) :=
    (isOpen_lt Complex.UnitDisc.continuous_coe.norm continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [hN] with z hzε
  rw [cornerOpenRadialSector_closure a b ε hab hε]
  constructor
  · rintro ⟨⟨r,t⟩,⟨hr,ht⟩,he⟩
    by_cases hr0 : r=0
    · left
      apply Complex.UnitDisc.coe_injective
      simpa only [hr0,Complex.ofReal_zero,zero_mul,Complex.UnitDisc.coe_zero] using he.symm
    · have hrp : 0<r:=lt_of_le_of_ne hr.1 (Ne.symm hr0)
      have hnorm : r=‖(z:ℂ)‖ := by
        rw [←he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrp,Circle.norm_coe,mul_one]
      right
      refine ⟨⟨r,hrp,by rw [hnorm];exact z.norm_lt_one⟩,Circle.exp t,?_,?_⟩
      · rw [hA]
        exact ⟨t,ht,rfl⟩
      · exact Complex.UnitDisc.coe_injective he.symm
  · rintro (rfl|⟨r,u,hu,he⟩)
    · refine ⟨(0,a),⟨⟨le_rfl,hε.le⟩,⟨le_rfl,hab.le⟩⟩,by simp⟩
    · rw [hA] at hu
      obtain ⟨t,ht,htu⟩ := hu
      have hnorm : r.val=‖(z:ℂ)‖ := by
        rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint_norm]
      refine ⟨(r.val,t),⟨⟨r.property.1.le,by rw [hnorm];exact hzε.le⟩,ht⟩,?_⟩
      change (r.val:ℂ)*(Circle.exp t:ℂ)=(z:ℂ)
      rw [htu]
      exact congrArg (fun w : 𝔻=>(w:ℂ)) he.symm


/-- Equality with a genuine small open radial sector identifies the actual
disc closure germ, using the existing open embedding of the disc. -/
theorem local_sector_closure_disc_germ {I : Set ℂ} (a b ε : ℝ)
    (hab : a<b) (hε : 0<ε)
    (heq : I∩Metric.ball (0:ℂ) ε=cornerOpenRadialSector a b ε) :
    ∀ᶠ (z : 𝔻) in 𝓝 (0:𝔻),
      z∈closure (((↑) : 𝔻→ℂ) ⁻¹' I) ↔
      z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector ((((a+b)/2:ℝ):AddCircle (2*Real.pi))) ((b-a)/2) := by
  have hIgerm : ∀ᶠz in 𝓝 (0:ℂ),z∈I ↔ z∈cornerOpenRadialSector a b ε := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hε] with z hz
    have hh:=congrArg (fun S : Set ℂ=>z∈S) heq
    simpa only [mem_inter_iff,hz,and_true] using (iff_of_eq hh)
  have hcl:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hIgerm
  have hcoe : Tendsto ((↑) : 𝔻→ℂ) (𝓝 (0:𝔻)) (𝓝 (0:ℂ)) := by
    simpa only [Complex.UnitDisc.coe_zero] using
      (Complex.UnitDisc.continuous_coe.continuousAt (x:=(0:𝔻))).tendsto
  have hclD:=hcoe.eventually hcl
  filter_upwards [hclD,cornerOpenRadialSector_closure_disc_germ a b ε hab hε] with z hz hS
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coe_isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    Complex.UnitDisc.continuous_coe]
  exact hz.trans hS

/-- Two genuinely open complementary regions with an actual two-ray germ
at their common frontier select one real closed angular sector, including
all reflex and straight cases. Only the local complement relation is needed. -/
theorem two_open_regions_corner_sector {I O : Set ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O)
    (h0I : (0:ℂ)∈frontier I) (h0O : (0:ℂ)∈frontier O)
    (u v : Circle) (hne : u≠v)
    (hcomp : ∀ᶠz in 𝓝 (0:ℂ),z∈I∪O ↔ z∉cornerNonnegativeRay u∪cornerNonnegativeRay v) :
    ∃a r : ℝ,0<r ∧ r<Real.pi ∧
      (∀ᶠ (z : 𝔻) in 𝓝 (0:𝔻),
        z∈closure (((↑) : 𝔻→ℂ) ⁻¹'
          I) ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector (a:AddCircle (2*Real.pi)) r) ∧
      ({Circle.exp (a-r),Circle.exp (a+r)} : Set Circle)={u,v} := by
  obtain ⟨a,b,hab,hba,ha,hb⟩ := circle_distinct_ordered_lifts u v hne
  have hcomp' : ∀ᶠz in 𝓝 (0:ℂ),z∈I∪O ↔
      z∉cornerNonnegativeRay (Circle.exp a)∪cornerNonnegativeRay (Circle.exp b) := by
    simpa only [ha,hb] using hcomp
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hcomp'
  have hlocal : (I∪O)∩Metric.ball (0:ℂ) ε=Metric.ball (0:ℂ) ε\
      (cornerNonnegativeRay (Circle.exp a)∪cornerNonnegativeRay (Circle.exp b)) := by
    ext z
    constructor
    · rintro ⟨hz,hzε⟩
      exact ⟨hzε,(hεsub hzε).mp hz⟩
    · rintro ⟨hzε,hz⟩
      exact ⟨(hεsub hzε).mpr hz,hzε⟩
  have hpart:=two_frontier_regions_local_partition hI hO hd hlocal h0I h0O
    (Metric.ball_mem_nhds (0:ℂ) hε) (cornerOpenRadialSector_two_partition a b ε hab hba)
    (cornerOpenRadialSector_preconnected a b ε)
    (cornerOpenRadialSector_preconnected b (a+2*Real.pi) ε)
  rcases hpart with hp|hp
  · refine ⟨(a+b)/2,(b-a)/2,by linarith,by linarith,
      local_sector_closure_disc_germ a b ε hab hε hp,?_⟩
    rw [show (a+b)/2-(b-a)/2=a by ring,show (a+b)/2+(b-a)/2=b by ring,ha,hb]
  · refine ⟨(b+(a+2*Real.pi))/2,((a+2*Real.pi)-b)/2,by linarith,by linarith,
      local_sector_closure_disc_germ b (a+2*Real.pi) ε hba hε hp,?_⟩
    rw [show (b+(a+2*Real.pi))/2-((a+2*Real.pi)-b)/2=b by ring,
      show (b+(a+2*Real.pi))/2+((a+2*Real.pi)-b)/2=a+2*Real.pi by ring,
      Circle.exp_add_two_pi,ha,hb,pair_comm]

/-- A true Jordan boundary with precisely two different actual nonnegative
ray germs bounds one genuine closed angular sector near its vertex. -/
theorem complexJordan_corner_sector {C : Set ℂ} (hC : IsComplexJordanCurve C)
    (u v : Circle) (hne : u≠v)
    (hboundary : ∀ᶠz in 𝓝 (0:ℂ),z∈C ↔
      (∃t : ℝ,0≤t ∧ z=(t:ℂ)*(u:ℂ)) ∨(∃t : ℝ,0≤t ∧ z=(t:ℂ)*(v:ℂ))) :
    ∃a r : ℝ,0<r ∧ r<Real.pi ∧
      (∀ᶠ (z : 𝔻) in 𝓝 (0:𝔻),
        z∈closure (((↑) : 𝔻→ℂ) ⁻¹' complexJordanInside C) ↔
          z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector (a:AddCircle (2*Real.pi)) r) ∧
      ({Circle.exp (a-r),Circle.exp (a+r)} : Set Circle)={u,v} := by
  have h0 : (0:ℂ)∈C:=hboundary.self_of_nhds.mpr (Or.inl ⟨0,le_rfl,by simp⟩)
  obtain ⟨hI,hO,hd,hcover,_hIc,_hOc,hFI,hFO⟩ := complexJordan_regions hC
  apply two_open_regions_corner_sector hI hO hd (hFI.symm ▸ h0) (hFO.symm ▸ h0) u v hne
  filter_upwards [hboundary] with z hz
  rw [hcover]
  exact not_congr hz


/-- The local two-ray sector conclusion works directly for the two genuine
open regions in the native disc. A global complex Jordan image is unnecessary. -/
theorem disc_two_open_regions_corner_sector {U V : Set 𝔻}
    (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (h0U : (0:𝔻)∈frontier U) (h0V : (0:𝔻)∈frontier V)
    (u v : Circle) (hne : u≠v)
    (hcomp : ∀ᶠ (z : 𝔻) in 𝓝 (0:𝔻),z∈U∪V ↔
      (z:ℂ)∉cornerNonnegativeRay u∪cornerNonnegativeRay v) :
    ∃a r : ℝ,0<r ∧ r<Real.pi ∧
      (∀ᶠ (z : 𝔻) in 𝓝 (0:𝔻),z∈closure U ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector
        (a:AddCircle (2*Real.pi)) r) ∧
      ({Circle.exp (a-r),Circle.exp (a+r)} : Set Circle)={u,v} := by
  let I:=((↑) : 𝔻→ℂ) '' U
  let O:=((↑) : 𝔻→ℂ) '' V
  have hI : IsOpen I:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coe_isOpenEmbedding.isOpenMap U hU
  have hO : IsOpen O:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coe_isOpenEmbedding.isOpenMap V hV
  have hIO : Disjoint I O := by
    apply disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy:=Complex.UnitDisc.coe_injective (hxz.trans hyz.symm)
    exact disjoint_left.mp hd hx (hxy.symm ▸ hy)
  have hfront (S : Set 𝔻) (hS : IsOpen S) (h0S : (0:𝔻)∈frontier S) :
      (0:ℂ)∈frontier (((↑) : 𝔻→ℂ) '' S) := by
    have hsimage:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coe_isOpenEmbedding.isOpenMap S hS
    rw [frontier,hS.interior_eq] at h0S
    rw [frontier,hsimage.interior_eq]
    constructor
    · have hh:=image_closure_subset_closure_image (s:=S) Complex.UnitDisc.continuous_coe
      have hm : ((0:𝔻):ℂ)∈((↑) : 𝔻→ℂ) '' closure S:=⟨0,h0S.1,rfl⟩
      simpa only [Complex.UnitDisc.coe_zero] using hh hm
    · rintro ⟨z,hz,hz0⟩
      have hz0' : z=(0:𝔻):=Complex.UnitDisc.coe_injective (by simpa only [Complex.UnitDisc.coe_zero] using hz0)
      exact h0S.2 (hz0' ▸ hz)
  have hcomp' : ∀ᶠz in 𝓝 (0:ℂ),z∈I∪O ↔z∉cornerNonnegativeRay u∪cornerNonnegativeRay v := by
    have hmap : Filter.map ((↑) : 𝔻→ℂ) (𝓝 (0:𝔻))=𝓝 (0:ℂ) := by
      simpa only [Complex.UnitDisc.coe_zero] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coe_isOpenEmbedding.map_nhds_eq (0:𝔻)
    rw [←hmap]
    change ∀ᶠ (z : 𝔻) in 𝓝 (0:𝔻),
      (z:ℂ)∈I∪O ↔(z:ℂ)∉cornerNonnegativeRay u∪cornerNonnegativeRay v
    filter_upwards [hcomp] with z hz
    have hm : (z:ℂ)∈I∪O ↔z∈U∪V := by
      change (z:ℂ)∈((↑) : 𝔻→ℂ) '' U∪((↑) : 𝔻→ℂ) '' V ↔_
      rw [←image_union]
      exact Complex.UnitDisc.coe_injective.mem_set_image
    exact hm.trans hz
  obtain ⟨a,r,hr,hrπ,hgerm,hends⟩ := two_open_regions_corner_sector hI hO hIO
    (hfront U hU h0U) (hfront V hV h0V) u v hne hcomp'
  refine ⟨a,r,hr,hrπ,?_,hends⟩
  simpa only [I,preimage_image_eq _ Complex.UnitDisc.coe_injective] using hgerm

end LowDimensionalTopology.Geometry.Polygon
