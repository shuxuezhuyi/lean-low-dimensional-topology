/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralSectors
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralGroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped ComplexConjugate
namespace LowDimensionalTopology.Geometry.Euclidean

/-- The only mixed closed-chamber coincidences are the two literal boundary rays. -/
theorem finiteDihedral_closedArc_mixed_eq (n : ℕ) (hn : 0<n) (k l : ℤ) (s t : ℝ)
    (hs : s∈Icc (0:ℝ) (finiteRotationPeriod n/2))
    (ht : t∈Icc (0:ℝ) (finiteRotationPeriod n/2))
    (he : finiteRotationGenerator n^k*Circle.exp s=finiteRotationGenerator n^l*(Circle.exp t)⁻¹) :
    (s=0 ∧ t=0 ∧ finiteRotationGenerator n^k=finiteRotationGenerator n^l) ∨
    (s=finiteRotationPeriod n/2 ∧ t=finiteRotationPeriod n/2 ∧
      finiteRotationGenerator n^k=finiteRotationGenerator n^(l-1)) := by
  have hP:=finiteRotationPeriod_pos n hn
  by_cases ht0 : t=0
  · subst t
    have he' : finiteRotationGenerator n^k*Circle.exp s=finiteRotationGenerator n^l*Circle.exp 0:=by
      simpa only [Circle.exp_zero,inv_one] using he
    have hu:=finiteRotation_halfOpenArc_unique n hn k l s 0
      ⟨hs.1,by linarith [hs.2]⟩ ⟨le_refl _,hP⟩ he'
    exact Or.inl ⟨hu.1,rfl,hu.2⟩
  · have htpos : 0<t:=lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have he' : finiteRotationGenerator n^k*Circle.exp s=
        finiteRotationGenerator n^(l-1)*Circle.exp (finiteRotationPeriod n-t):=by
      calc
        _=finiteRotationGenerator n^l*(Circle.exp t)⁻¹:=he
        _=finiteRotationGenerator n^(l-1)*(finiteRotationGenerator n*(Circle.exp t)⁻¹):=by
          have hl : finiteRotationGenerator n^l=finiteRotationGenerator n^(l-1)*finiteRotationGenerator n:=by
            calc _=finiteRotationGenerator n^((l-1)+1):=by congr 1;omega
                 _=finiteRotationGenerator n^(l-1)*finiteRotationGenerator n:=by rw [zpow_add,zpow_one]
          rw [hl,mul_assoc]
        _=finiteRotationGenerator n^(l-1)*Circle.exp (finiteRotationPeriod n-t):=by
          change finiteRotationGenerator n^(l-1)*(Circle.exp (finiteRotationPeriod n)*(Circle.exp t)⁻¹)=_
          rw [←Circle.exp_neg,←Circle.exp_add]
          rfl
    have hu:=finiteRotation_halfOpenArc_unique n hn k (l-1) s (finiteRotationPeriod n-t)
      ⟨hs.1,by linarith [hs.2]⟩ ⟨by linarith [ht.2],by linarith⟩ he'
    exact Or.inr ⟨by linarith [hs.2,ht.2,hu.1],by linarith [hs.2,ht.2,hu.1],hu.2⟩

/-- Closed fundamental arcs meet every genuine dihedral orbit in a unique point. -/
theorem finiteDihedral_closedArc_orbit_unique (n : ℕ) (hn : 0<n) (i j : Fin n) (b c : Bool)
    (s t : ℝ) (hs : s∈Icc (0:ℝ) (finiteRotationPeriod n/2))
    (ht : t∈Icc (0:ℝ) (finiteRotationPeriod n/2))
    (he : finiteDihedralCircleAction n i b (Circle.exp s)=
      finiteDihedralCircleAction n j c (Circle.exp t)) : s=t := by
  have hP:=finiteRotationPeriod_pos n hn
  cases b <;> cases c
  · exact (finiteRotation_halfOpenArc_unique n hn (i.val:ℤ) (j.val:ℤ) s t
      ⟨hs.1,by linarith [hs.2]⟩ ⟨ht.1,by linarith [ht.2]⟩ (by simpa only
        [zpow_natCast,finiteDihedralCircleAction,Bool.false_eq_true,ite_false,ite_true] using he)).1
  · have hm:=finiteDihedral_closedArc_mixed_eq n hn (i.val:ℤ) (j.val:ℤ) s t hs ht
      (by simpa only [zpow_natCast,finiteDihedralCircleAction,Bool.false_eq_true,ite_false,ite_true] using he)
    rcases hm with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> rfl
  · have hm:=finiteDihedral_closedArc_mixed_eq n hn (j.val:ℤ) (i.val:ℤ) t s ht hs
      (by simpa only [zpow_natCast,finiteDihedralCircleAction,Bool.false_eq_true,ite_false,ite_true] using he.symm)
    rcases hm with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> rfl
  · have he' : finiteRotationGenerator n^(-(i.val:ℤ))*Circle.exp s=
        finiteRotationGenerator n^(-(j.val:ℤ))*Circle.exp t:=by
      simpa only [finiteDihedralCircleAction,ite_true,mul_inv_rev,inv_inv,zpow_neg,
        zpow_natCast,mul_comm] using congrArg Inv.inv he
    exact (finiteRotation_halfOpenArc_unique n hn (-(i.val:ℤ)) (-(j.val:ℤ)) s t
      ⟨hs.1,by linarith [hs.2]⟩ ⟨ht.1,by linarith [ht.2]⟩ he').1

/-- The literal closed wedge has its genuine radial coordinate description. -/
theorem finiteDihedral_closedPlaneSector_mem_iff (n : ℕ) (z : ℂ) :
    z∈finiteRotationClosedPlaneSector (2*n) ↔
      z=0 ∨ ∃r : ℝ,0<r ∧ ∃t∈Icc (0:ℝ) (finiteRotationPeriod n/2),
        z=(r:ℂ)*(Circle.exp t:ℂ) := by
  constructor
  · rintro (rfl|⟨w,hw,rfl⟩)
    · exact Or.inl rfl
    · right
      change finiteSectorDirection w∈finiteRotationClosedArc (2*n) at hw
      rw [←finiteDihedralClosedArc_eq] at hw
      obtain ⟨t,ht,he⟩:=hw
      refine ⟨‖w.val‖,norm_pos_iff.mpr w.property,t,ht,?_⟩
      rw [he]
      exact (finiteSectorDirection_reconstruct w).symm
  · rintro (rfl|⟨r,hr,t,ht,rfl⟩)
    · exact Or.inl rfl
    · apply finiteRotationClosedPlaneSector_radial (2*n) r hr (Circle.exp t)
      rw [←finiteDihedralClosedArc_eq]
      exact ⟨t,ht,rfl⟩

/-- A genuine dihedral orbit meets the original closed planar wedge in a single point. -/
theorem finiteDihedral_closedPlaneSector_orbit_unique (n : ℕ) (hn : 0<n)
    (i j : Fin n) (b c : Bool) (x y : ℂ)
    (hx : x∈finiteRotationClosedPlaneSector (2*n))
    (hy : y∈finiteRotationClosedPlaneSector (2*n))
    (he : finiteDihedralPlaneAction n i b x=finiteDihedralPlaneAction n j c y) : x=y := by
  have hnxy : ‖x‖=‖y‖:=by
    simpa only [finiteDihedralPlaneAction_norm] using congrArg norm he
  rcases (finiteDihedral_closedPlaneSector_mem_iff n x).mp hx with rfl|⟨r,hr,s,hs,rfl⟩
  · exact (norm_eq_zero.mp (by simpa using hnxy.symm)).symm
  · rcases (finiteDihedral_closedPlaneSector_mem_iff n y).mp hy with rfl|⟨q,hq,t,ht,rfl⟩
    · exact norm_eq_zero.mp (by simpa using hnxy)
    · have hrq : r=q:=by
        simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,abs_of_pos hq,
          Circle.norm_coe,mul_one] using hnxy
      subst q
      rw [finiteDihedralPlaneAction_radial,finiteDihedralPlaneAction_radial] at he
      have hc : finiteDihedralCircleAction n i b (Circle.exp s)=
          finiteDihedralCircleAction n j c (Circle.exp t):=
        Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') he)
      rw [finiteDihedral_closedArc_orbit_unique n hn i j b c s t hs ht hc]

/-- Away from the vertex, the only nonidentity chamber stabilizers are its actual two mirrors. -/
theorem finitePlanarDihedral_chamber_stabilizer (n : ℕ) (hn : 0<n)
    (g : ℂ ≃ₗᵢ[ℝ] ℂ) (hg : g∈finitePlanarDihedralGroup n)
    (x : ℂ) (hx : x∈finiteRotationClosedPlaneSector (2*n)) (hx0 : x≠0)
    (hfix : g x=x) :
    g=1 ∨
      (g=finitePlanarOrthogonalMap 1 true ∧ finitePlanarOrthogonalMap 1 true x=x) ∨
      (g=finitePlanarOrthogonalMap (finiteRotationGenerator n) true ∧
        finitePlanarOrthogonalMap (finiteRotationGenerator n) true x=x) := by
  obtain ⟨k,b,rfl⟩:=finitePlanarDihedralGroup_normal_form n g hg
  cases b
  · have hu : (finiteRotationGenerator n^k:Circle)=1:=Circle.ext (by
      apply mul_right_cancel₀ hx0
      simpa only [finitePlanarOrthogonalMap_apply,Bool.false_eq_true,ite_false,Circle.coe_one,
        one_mul] using hfix)
    left
    rw [hu,finitePlanarOrthogonalMap_one]
  · rcases (finiteDihedral_closedPlaneSector_mem_iff n x).mp hx with hx|⟨r,hr,t,ht,rfl⟩
    · exact False.elim (hx0 hx)
    · have he : finiteRotationGenerator n^k*(Circle.exp t)⁻¹=Circle.exp t := by
        apply Circle.ext
        apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
        change (r:ℂ)*((finiteRotationGenerator n^k:Circle)*(Circle.exp t)⁻¹)=
          (r:ℂ)*(Circle.exp t)
        calc
          _=(finiteRotationGenerator n^k:Circle)*conj ((r:ℂ)*(Circle.exp t:ℂ)):=by
            rw [Circle.coe_inv_eq_conj,map_mul,Complex.conj_ofReal]
            ring
          _=(r:ℂ)*(Circle.exp t:ℂ):=hfix
      have hm:=finiteDihedral_closedArc_mixed_eq n hn 0 k t t ht ht (by
        simpa only [zpow_zero,one_mul] using he.symm)
      rcases hm with ⟨_,_,hp⟩|⟨_,_,hp⟩
      · have hu : finiteRotationGenerator n^k=1:=by simpa only [zpow_zero] using hp.symm
        right;left
        exact ⟨by rw [hu],by simpa only [hu] using hfix⟩
      · have hp' : finiteRotationGenerator n^(k-1)=1:=by simpa only [zpow_zero] using hp.symm
        have hu : finiteRotationGenerator n^k=finiteRotationGenerator n:=by
          calc _=finiteRotationGenerator n^((k-1)+1):=by congr 1;omega
               _=finiteRotationGenerator n^(k-1)*finiteRotationGenerator n:=by rw [zpow_add,zpow_one]
               _=finiteRotationGenerator n:=by rw [hp',one_mul]
        right;right
        exact ⟨by rw [hu],by simpa only [hu] using hfix⟩

theorem finitePlanarOrthogonalMap_dihedral_action (n : ℕ) (i : Fin n) (b : Bool) (z : ℂ) :
    finitePlanarOrthogonalMap (finiteRotationGenerator n^i.val) b z=
      finiteDihedralPlaneAction n i b z := by
  cases b <;> rfl

/-- The original closed wedge is a unique representative set for the genuine generated group. -/
theorem finitePlanarDihedral_closed_chamber_unique (n : ℕ) (hn : 0<n)
    (g h : ℂ ≃ₗᵢ[ℝ] ℂ) (hg : g∈finitePlanarDihedralGroup n) (hh : h∈finitePlanarDihedralGroup n)
    (x y : ℂ) (hx : x∈finiteRotationClosedPlaneSector (2*n))
    (hy : y∈finiteRotationClosedPlaneSector (2*n)) (he : g x=h y) : x=y := by
  obtain ⟨k,b,hg'⟩:=finitePlanarDihedralGroup_normal_form n g hg
  obtain ⟨l,c,hh'⟩:=finitePlanarDihedralGroup_normal_form n h hh
  obtain ⟨i,hi⟩:=finiteRotationGenerator_zpow_eq_fin n hn k
  obtain ⟨j,hj⟩:=finiteRotationGenerator_zpow_eq_fin n hn l
  apply finiteDihedral_closedPlaneSector_orbit_unique n hn i j b c x y hx hy
  simpa only [hg',hh',hi,hj,finitePlanarOrthogonalMap_dihedral_action] using he

/-- Every nonvertex local coincidence is exactly an original boundary-mirror gluing. -/
theorem finitePlanarDihedral_chamber_coincidence (n : ℕ) (hn : 0<n)
    (g h : ℂ ≃ₗᵢ[ℝ] ℂ) (hg : g∈finitePlanarDihedralGroup n) (hh : h∈finitePlanarDihedralGroup n)
    (x y : ℂ) (hx : x∈finiteRotationClosedPlaneSector (2*n))
    (hy : y∈finiteRotationClosedPlaneSector (2*n)) (he : g x=h y) :
    x=y ∧ (x=0 ∨ g=h ∨ ∃R : ℂ ≃ₗᵢ[ℝ] ℂ,
      (R=finitePlanarOrthogonalMap 1 true ∨ R=finitePlanarOrthogonalMap (finiteRotationGenerator n) true) ∧
      R x=x ∧ g=h*R) := by
  have hxy:=finitePlanarDihedral_closed_chamber_unique n hn g h hg hh x y hx hy he
  refine ⟨hxy,?_⟩
  subst y
  by_cases hx0 : x=0
  · exact Or.inl hx0
  · right
    have hq : h⁻¹*g∈finitePlanarDihedralGroup n:=
      (finitePlanarDihedralGroup n).mul_mem ((finitePlanarDihedralGroup n).inv_mem hh) hg
    have hqfix : (h⁻¹*g) x=x := by
      change h.symm (g x)=x
      rw [he,h.symm_apply_apply]
    rcases finitePlanarDihedral_chamber_stabilizer n hn (h⁻¹*g) hq x hx hx0 hqfix with
      h1|⟨h0,hfixed⟩|⟨h1,hfixed⟩
    · left
      calc g=h*(h⁻¹*g):=by group
           _=h:=by rw [h1,mul_one]
    · right
      refine ⟨finitePlanarOrthogonalMap 1 true,Or.inl rfl,hfixed,?_⟩
      calc g=h*(h⁻¹*g):=by group
           _=h*finitePlanarOrthogonalMap 1 true:=by rw [h0]
    · right
      refine ⟨finitePlanarOrthogonalMap (finiteRotationGenerator n) true,Or.inr rfl,hfixed,?_⟩
      calc g=h*(h⁻¹*g):=by group
           _=h*finitePlanarOrthogonalMap (finiteRotationGenerator n) true:=by rw [h1]

end LowDimensionalTopology.Geometry.Euclidean
