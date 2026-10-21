/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteRotationSectors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped ComplexConjugate
namespace LowDimensionalTopology.Geometry.Euclidean

/-- The literal angular wedge bounded by two reflecting lines of angle pi/n. -/
def finiteDihedralOpenArc (n : ℕ) : Set Circle :=
  Circle.exp '' Ioo 0 (finiteRotationPeriod n/2)

def finiteDihedralClosedArc (n : ℕ) : Set Circle :=
  Circle.exp '' Icc 0 (finiteRotationPeriod n/2)

/-- Rotation followed, when b is true, by the actual conjugation of the circle. -/
def finiteDihedralCircleAction (n : ℕ) (i : Fin n) (b : Bool) (z : Circle) : Circle :=
  finiteRotationGenerator n^i.val * (if b then z⁻¹ else z)

theorem finiteDihedralOpenArc_isOpen (n : ℕ) : IsOpen (finiteDihedralOpenArc n) :=
  Circle.isCoveringMap_exp.isOpenMap _ isOpen_Ioo

theorem finiteDihedralOpenArc_closure (n : ℕ) (hn : 0<n) :
    closure (finiteDihedralOpenArc n)=finiteDihedralClosedArc n := by
  have hP : 0<finiteRotationPeriod n/2:=half_pos (finiteRotationPeriod_pos n hn)
  apply subset_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_Icc.image Circle.exp.continuous).isClosed
  · have h:=image_closure_subset_closure_image (s:=Ioo (0:ℝ) (finiteRotationPeriod n/2))
        Circle.exp.continuous
    rw [closure_Ioo hP.ne] at h
    exact h

/-- The two reflected half-periods, under the actual n rotations, cover the circle. -/
theorem finiteDihedral_closedArc_finite_cover (n : ℕ) (hn : 0<n) :
    (⋃(i : Fin n)(b : Bool),finiteDihedralCircleAction n i b '' finiteDihedralClosedArc n)=univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨k,t,ht,hz⟩:=finiteRotation_halfOpenArc_cover n hn z
  have hP:=finiteRotationPeriod_pos n hn
  by_cases hhalf : t≤finiteRotationPeriod n/2
  · obtain ⟨i,hi⟩:=finiteRotationGenerator_zpow_eq_fin n hn k
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨false,Circle.exp t,⟨t,⟨ht.1,hhalf⟩,rfl⟩,?_⟩⟩
    change finiteRotationGenerator n^i.val*Circle.exp t=z
    rw [←hi]
    exact hz.symm
  · obtain ⟨i,hi⟩:=finiteRotationGenerator_zpow_eq_fin n hn (k+1)
    let s:=finiteRotationPeriod n-t
    have hs : s∈Icc (0:ℝ) (finiteRotationPeriod n/2):=by
      dsimp only [s]
      constructor
      · linarith [ht.2]
      · linarith
    have he : Circle.exp t=Circle.exp (finiteRotationPeriod n)*(Circle.exp s)⁻¹:=by
      rw [←Circle.exp_neg,←Circle.exp_add]
      congr 1
      dsimp only [s]
      ring
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨true,Circle.exp s,⟨s,hs,rfl⟩,?_⟩⟩
    change finiteRotationGenerator n^i.val*(Circle.exp s)⁻¹=z
    rw [←hi,hz,he,zpow_add,zpow_one]
    exact mul_assoc _ _ _

/-- An actual open dihedral wedge cannot meet a reflected open wedge. -/
theorem finiteDihedral_positive_negative_disjoint (n : ℕ) (hn : 0<n) (k l : ℤ) :
    Disjoint ((fun z : Circle=>finiteRotationGenerator n^k*z) '' finiteDihedralOpenArc n)
      ((fun z : Circle=>finiteRotationGenerator n^l*z⁻¹) '' finiteDihedralOpenArc n) := by
  apply disjoint_left.mpr
  rintro z ⟨_,⟨s,hs,rfl⟩,rfl⟩ ⟨_,⟨t,ht,rfl⟩,he⟩
  have hP:=finiteRotationPeriod_pos n hn
  have he' : finiteRotationGenerator n^k*Circle.exp s=
      finiteRotationGenerator n^(l-1)*Circle.exp (finiteRotationPeriod n-t):=by
    calc
      _=finiteRotationGenerator n^l*(Circle.exp t)⁻¹:=he.symm
      _=finiteRotationGenerator n^(l-1)*(finiteRotationGenerator n* (Circle.exp t)⁻¹):=by
        have hl : finiteRotationGenerator n^l=finiteRotationGenerator n^(l-1)*finiteRotationGenerator n:=by
          calc _=finiteRotationGenerator n^((l-1)+1):=by congr 1;omega
               _=finiteRotationGenerator n^(l-1)*finiteRotationGenerator n:=by rw [zpow_add,zpow_one]
        rw [hl,mul_assoc]
      _=finiteRotationGenerator n^(l-1)*Circle.exp (finiteRotationPeriod n-t):=by
        change finiteRotationGenerator n^(l-1)*(Circle.exp (finiteRotationPeriod n)*(Circle.exp t)⁻¹)=_
        rw [←Circle.exp_neg,←Circle.exp_add]
        rfl
  have hst:=(finiteRotation_halfOpenArc_unique n hn k (l-1) s (finiteRotationPeriod n-t)
    ⟨hs.1.le,by linarith [hs.2]⟩ ⟨by linarith [ht.2],by linarith [ht.1]⟩ he').1
  linarith [hs.2,ht.2]

/-- Actual dihedral images of the open half-period have disjoint interiors. -/
theorem finiteDihedral_openArc_finite_disjoint (n : ℕ) (hn : 0<n) :
    Pairwise (fun a b : Fin n×Bool=>Disjoint
      (finiteDihedralCircleAction n a.1 a.2 '' finiteDihedralOpenArc n)
      (finiteDihedralCircleAction n b.1 b.2 '' finiteDihedralOpenArc n)) := by
  rintro ⟨i,bi⟩ ⟨j,bj⟩ hne
  have hP:=finiteRotationPeriod_pos n hn
  cases bi <;> cases bj
  · apply disjoint_left.mpr
    rintro z ⟨_,⟨s,hs,rfl⟩,rfl⟩ ⟨_,⟨t,ht,rfl⟩,he⟩
    have hij : i=j:=finiteRotationGenerator_pow_fin_injective n hn
      (by simpa only [zpow_natCast] using
        (finiteRotation_halfOpenArc_unique n hn (i.val:ℤ) (j.val:ℤ) s t
          ⟨hs.1.le,by linarith [hs.2]⟩ ⟨ht.1.le,by linarith [ht.2]⟩ he.symm).2)
    exact hne (by simp [hij])
  · simpa only [finiteDihedralCircleAction,Bool.false_eq_true,ite_false,ite_true,zpow_natCast]
      using finiteDihedral_positive_negative_disjoint n hn (i.val:ℤ) (j.val:ℤ)
  · simpa only [finiteDihedralCircleAction,Bool.false_eq_true,ite_false,ite_true,zpow_natCast]
      using (finiteDihedral_positive_negative_disjoint n hn (j.val:ℤ) (i.val:ℤ)).symm
  · apply disjoint_left.mpr
    rintro z ⟨_,⟨s,hs,rfl⟩,rfl⟩ ⟨_,⟨t,ht,rfl⟩,he⟩
    have he' : finiteRotationGenerator n^(-(i.val:ℤ))*Circle.exp s=
        finiteRotationGenerator n^(-(j.val:ℤ))*Circle.exp t:=by
      have h:=congrArg Inv.inv he.symm
      simpa only [finiteDihedralCircleAction,ite_true,mul_inv_rev,inv_inv,zpow_neg,
        zpow_natCast,mul_comm] using h
    have hp:=(finiteRotation_halfOpenArc_unique n hn (-(i.val:ℤ)) (-(j.val:ℤ)) s t
      ⟨hs.1.le,by linarith [hs.2]⟩ ⟨ht.1.le,by linarith [ht.2]⟩ he').2
    have hij : i=j:=finiteRotationGenerator_pow_fin_injective n hn (by
      simpa only [zpow_neg,zpow_natCast,inv_inv] using congrArg Inv.inv hp)
    exact hne (by simp [hij])

theorem finiteRotationPeriod_double (n : ℕ) :
    finiteRotationPeriod (2*n)=finiteRotationPeriod n/2 := by
  by_cases hn : n=0
  · simp [hn,finiteRotationPeriod]
  · dsimp only [finiteRotationPeriod]
    push_cast
    field_simp

theorem finiteDihedralOpenArc_eq (n : ℕ) :
    finiteDihedralOpenArc n=finiteRotationOpenArc (2*n) := by
  simp only [finiteDihedralOpenArc,finiteRotationOpenArc,finiteRotationPeriod_double]

theorem finiteDihedralClosedArc_eq (n : ℕ) :
    finiteDihedralClosedArc n=finiteRotationClosedArc (2*n) := by
  simp only [finiteDihedralClosedArc,finiteRotationClosedArc,finiteRotationPeriod_double]

/-- Literal rotations and complex conjugations on the original plane. -/
def finiteDihedralPlaneAction (n : ℕ) (i : Fin n) (b : Bool) (z : ℂ) : ℂ :=
  (finiteRotationGenerator n^i.val:Circle)*(if b then conj z else z)

theorem finiteDihedralPlaneAction_radial (n : ℕ) (i : Fin n) (b : Bool) (r : ℝ) (u : Circle) :
    finiteDihedralPlaneAction n i b ((r:ℂ)*(u:ℂ))=
      (r:ℂ)*(finiteDihedralCircleAction n i b u:ℂ) := by
  cases b
  · change _*((r:ℂ)*(u:ℂ))=(r:ℂ)*(_*(u:ℂ))
    ring
  · change _*conj ((r:ℂ)*(u:ℂ))=(r:ℂ)*(_*(u⁻¹:Circle))
    rw [Circle.coe_inv_eq_conj,map_mul,Complex.conj_ofReal]
    ring

theorem finiteDihedralPlaneAction_norm (n : ℕ) (i : Fin n) (b : Bool) (z : ℂ) :
    ‖finiteDihedralPlaneAction n i b z‖=‖z‖ := by
  cases b <;> simp only [finiteDihedralPlaneAction,ite_true,Bool.false_eq_true,ite_false,
    norm_mul,Circle.norm_coe,one_mul,Complex.norm_conj]

/-- The actual finite dihedral wedges cover every point of the original plane. -/
theorem finiteDihedral_closedPlaneSector_finite_cover (n : ℕ) (hn : 0<n) :
    (⋃(i : Fin n)(b : Bool),finiteDihedralPlaneAction n i b ''
      finiteRotationClosedPlaneSector (2*n))=univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : z=0
  · subst z
    refine mem_iUnion.mpr ⟨⟨0,hn⟩,mem_iUnion.mpr ⟨false,0,Or.inl rfl,?_⟩⟩
    simp only [finiteDihedralPlaneAction,Bool.false_eq_true,ite_false,mul_zero]
  · let w : {z : ℂ // z≠0}:=⟨z,hz⟩
    have hu : finiteSectorDirection w∈⋃(i : Fin n)(b : Bool),
        finiteDihedralCircleAction n i b '' finiteDihedralClosedArc n:=by
      rw [finiteDihedral_closedArc_finite_cover n hn]
      trivial
    obtain ⟨i,hu⟩:=mem_iUnion.mp hu
    obtain ⟨b,u,hu,he⟩:=mem_iUnion.mp hu
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨b,(‖z‖:ℂ)*(u:ℂ),?_,?_⟩⟩
    · apply finiteRotationClosedPlaneSector_radial (2*n) ‖z‖ (norm_pos_iff.mpr hz) u
      rwa [←finiteDihedralClosedArc_eq]
    · calc _=(‖z‖:ℂ)*(finiteDihedralCircleAction n i b u:ℂ):=
             finiteDihedralPlaneAction_radial n i b ‖z‖ u
           _=(‖z‖:ℂ)*(finiteSectorDirection w:ℂ):=congrArg (fun v : Circle=>(‖z‖:ℂ)*(v:ℂ)) he
           _=z:=finiteSectorDirection_reconstruct w

theorem finiteSectorDirection_conjugation (z : {z : ℂ // z≠0}) :
    finiteSectorDirection ⟨conj z.val,by simpa using z.property⟩=(finiteSectorDirection z)⁻¹ := by
  apply Circle.ext
  rw [Circle.coe_inv_eq_conj]
  change conj z.val/(‖conj z.val‖:ℂ)=conj (z.val/(‖z.val‖:ℂ))
  rw [map_div₀,Complex.conj_ofReal,Complex.norm_conj]

theorem finiteDihedralPlaneAction_ne_zero (n : ℕ) (i : Fin n) (b : Bool) (z : ℂ) (hz : z≠0) :
    finiteDihedralPlaneAction n i b z≠0 := by
  apply norm_ne_zero_iff.mp
  rw [finiteDihedralPlaneAction_norm]
  exact norm_ne_zero_iff.mpr hz

theorem finiteDihedralPlaneAction_direction (n : ℕ) (i : Fin n) (b : Bool)
    (z : {z : ℂ // z≠0}) :
    finiteSectorDirection ⟨finiteDihedralPlaneAction n i b z.val,
      finiteDihedralPlaneAction_ne_zero n i b z.val z.property⟩=
      finiteDihedralCircleAction n i b (finiteSectorDirection z) := by
  cases b
  · exact finiteSectorDirection_rotation (finiteRotationGenerator n^i.val) z
  · change finiteSectorDirection ⟨(finiteRotationGenerator n^i.val:Circle)*conj z.val,_⟩=
      finiteRotationGenerator n^i.val*(finiteSectorDirection z)⁻¹
    exact (finiteSectorDirection_rotation (finiteRotationGenerator n^i.val)
      ⟨conj z.val,by simpa using z.property⟩).trans
      (congrArg (fun u : Circle=>finiteRotationGenerator n^i.val*u) (finiteSectorDirection_conjugation z))

/-- Genuine reflected open planar wedges have pairwise disjoint interiors. -/
theorem finiteDihedral_openPlaneSector_finite_disjoint (n : ℕ) (hn : 0<n) :
    Pairwise (fun a b : Fin n×Bool=>Disjoint
      (finiteDihedralPlaneAction n a.1 a.2 '' finiteRotationPlaneSector (2*n))
      (finiteDihedralPlaneAction n b.1 b.2 '' finiteRotationPlaneSector (2*n))) := by
  intro a b hab
  apply disjoint_left.mpr
  rintro z ⟨_,⟨v,hv,rfl⟩,hy⟩ ⟨_,⟨w,hw,rfl⟩,hx⟩
  have he : finiteDihedralCircleAction n a.1 a.2 (finiteSectorDirection v)=
      finiteDihedralCircleAction n b.1 b.2 (finiteSectorDirection w):=by
    rw [←finiteDihedralPlaneAction_direction,←finiteDihedralPlaneAction_direction]
    exact congrArg finiteSectorDirection (Subtype.ext (hy.trans hx.symm))
  have hv' : finiteSectorDirection v∈finiteDihedralOpenArc n:=by rwa [finiteDihedralOpenArc_eq]
  have hw' : finiteSectorDirection w∈finiteDihedralOpenArc n:=by rwa [finiteDihedralOpenArc_eq]
  exact disjoint_left.mp (finiteDihedral_openArc_finite_disjoint n hn hab)
    ⟨finiteSectorDirection v,hv',rfl⟩ ⟨finiteSectorDirection w,hw',he.symm⟩

/-- Literal rotations and reflections tile each genuine centred Euclidean ball. -/
theorem finiteDihedral_closedPlaneSector_ball_cover (n : ℕ) (hn : 0<n) (R : ℝ) :
    (⋃(i : Fin n)(b : Bool),finiteDihedralPlaneAction n i b ''
      (finiteRotationClosedPlaneSector (2*n)∩Metric.ball 0 R))=Metric.ball 0 R := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,hz⟩:=mem_iUnion.mp hz
    obtain ⟨b,w,⟨_,hw⟩,rfl⟩:=mem_iUnion.mp hz
    simpa only [Metric.mem_ball,dist_zero_right,finiteDihedralPlaneAction_norm] using hw
  · intro hz
    have hu : z∈⋃(i : Fin n)(b : Bool),finiteDihedralPlaneAction n i b ''
        finiteRotationClosedPlaneSector (2*n):=by rw [finiteDihedral_closedPlaneSector_finite_cover n hn];trivial
    obtain ⟨i,hu⟩:=mem_iUnion.mp hu
    obtain ⟨b,w,hw,rfl⟩:=mem_iUnion.mp hu
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨b,w,⟨hw,?_⟩,rfl⟩⟩
    simpa only [Metric.mem_ball,dist_zero_right,finiteDihedralPlaneAction_norm] using hz

end LowDimensionalTopology.Geometry.Euclidean
