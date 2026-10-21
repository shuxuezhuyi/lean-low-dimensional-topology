/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianElementary
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementFunctions
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Three real roots of a genuine quadratic cannot be pairwise different. -/
theorem quadratic_three_roots (a b c x y z : ℝ) (ha : a≠0)
    (hx : a*x^2+b*x+c=0) (hy : a*y^2+b*y+c=0) (hz : a*z^2+b*z+c=0) :
    x=y ∨ x=z ∨ y=z := by
  have hxy : (x-y)*(a*(x+y)+b)=0:=by nlinarith only [hx,hy]
  have hxz : (x-z)*(a*(x+z)+b)=0:=by nlinarith only [hx,hz]
  rcases mul_eq_zero.mp hxy with he | he
  · exact Or.inl (sub_eq_zero.mp he)
  · rcases mul_eq_zero.mp hxz with hf | hf
    · exact Or.inr (Or.inl (sub_eq_zero.mp hf))
    · right;right
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show a*(y-z)=0 by nlinarith only [he,hf])).resolve_left ha

/-- The actual native hyperbolic sphere has its exact Euclidean conic equation. -/
theorem halfPlane_sphere_coordinate_equation (w z : ℍ) (r : ℝ) (hz : dist w z=r) :
    (z.re-w.re)^2+z.im^2+w.im^2=2*w.im*z.im*Real.cosh r := by
  have h:=UpperHalfPlane.cosh_dist' w z
  rw [hz] at h
  have he:=(eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) w.im_ne_zero) z.im_ne_zero)).mp h
  nlinarith only [he]

/-- A genuine horizontal horocycle meets an actual hyperbolic circle in at most two points. -/
theorem halfPlane_sphere_equal_height_three (w x y z : ℍ) (r : ℝ)
    (hx : dist w x=r) (hy : dist w y=r) (hz : dist w z=r)
    (hxy : y.im=x.im) (hxz : z.im=x.im) : x=y ∨ x=z ∨ y=z := by
  have heq (t : ℍ) (ht : dist w t=r) (him : t.im=x.im) :
      t.re^2+(-2*w.re)*t.re+(w.re^2+x.im^2+w.im^2-2*w.im*x.im*Real.cosh r)=0:=by
    have h:=halfPlane_sphere_coordinate_equation w t r ht
    rw [him] at h
    nlinarith only [h]
  rcases quadratic_three_roots 1 (-2*w.re) _ x.re y.re z.re (by norm_num)
    (by simpa only [one_mul] using heq x hx rfl)
    (by simpa only [one_mul] using heq y hy hxy)
    (by simpa only [one_mul] using heq z hz hxz) with h | h | h
  · left;exact UpperHalfPlane.ext (Complex.ext h hxy.symm)
  · right;left;exact UpperHalfPlane.ext (Complex.ext h hxz.symm)
  · right;right;exact UpperHalfPlane.ext (Complex.ext h (hxy.trans hxz.symm))

/-- A genuine ray through the Euclidean origin meets an actual hyperbolic circle in at most two points. -/
theorem halfPlane_sphere_equal_slope_three (w x y z : ℍ) (r ρ : ℝ)
    (hx : dist w x=r) (hy : dist w y=r) (hz : dist w z=r)
    (hRx : x.re=ρ*x.im) (hRy : y.re=ρ*y.im) (hRz : z.re=ρ*z.im) : x=y ∨ x=z ∨ y=z := by
  have heq (t : ℍ) (ht : dist w t=r) (hre : t.re=ρ*t.im) :
      (ρ^2+1)*t.im^2+(-2*(ρ*w.re+w.im*Real.cosh r))*t.im+(w.re^2+w.im^2)=0:=by
    have h:=halfPlane_sphere_coordinate_equation w t r ht
    rw [hre] at h
    nlinarith only [h]
  have hA : ρ^2+1≠0:=ne_of_gt (by positivity)
  rcases quadratic_three_roots (ρ^2+1) (-2*(ρ*w.re+w.im*Real.cosh r)) _ x.im y.im z.im hA
    (heq x hx hRx) (heq y hy hRy) (heq z hz hRz) with h | h | h
  · left;apply UpperHalfPlane.ext;apply Complex.ext
    · change x.re=y.re
      rw [hRx,hRy,h]
    · exact h
  · right;left;apply UpperHalfPlane.ext;apply Complex.ext
    · change x.re=z.re
      rw [hRx,hRz,h]
    · exact h
  · right;right;apply UpperHalfPlane.ext;apply Complex.ext
    · change y.re=z.re
      rw [hRy,hRz,h]
    · exact h

/-- An actual generator-invariant function is invariant under all integer powers. -/
theorem invariant_zpow_smul {G X Y : Type*} [Group G] [MulAction G X]
    (g : G) (I : X→Y) (hI : ∀ x,I (g•x)=I x) (n : ℤ) (x : X) : I (g^n•x)=I x := by
  have hinv (y : X) : I (g⁻¹•y)=I y:=by
    have h:=hI (g⁻¹•y)
    simpa only [smul_inv_smul] using h.symm
  apply zpow_induction_left (g:=g) (P:=fun a=>∀ y,I (a•y)=I y) ?_ ?_ ?_ n x
  · intro y;simp only [one_smul]
  · intro a ha y;rw [mul_smul,hI,ha]
  · intro a ha y;rw [mul_smul,hinv,ha]

/-- Native real conjugation intertwines every original integer power exactly. -/
theorem realSL_conjugate_zpow_smul (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (n : ℤ) (z : ℍ) :
    q•(A^n•z)=(q*A*q⁻¹)^n•(q•z) := by
  have he:=map_zpow (MulAut.conj q) A n
  change q*A^n*q⁻¹=(q*A*q⁻¹)^n at he
  rw [←he]
  simp only [mul_smul,inv_smul_smul]

/-- Actual conjugation transports a generator invariant to every orbit point. -/
theorem realSL_cyclic_conjugate_invariant (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (I : ℍ→ℝ) (hI : ∀ z,I ((q*A*q⁻¹)•z)=I z) (n : ℤ) (z : ℍ) :
    I (q•(A^n•z))=I (q•z) := by
  rw [realSL_conjugate_zpow_smul]
  exact invariant_zpow_smul (q*A*q⁻¹) I hI n (q•z)

/-- Genuine cyclic orbits normalized to horizontal horocycles have no three
pairwise distinct points on a genuine hyperbolic circle. -/
theorem realSL_cyclic_circle_of_height_invariant (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hI : ∀ z : ℍ,((q*A*q⁻¹)•z).im=z.im) (z w : ℍ) (m n k : ℤ) (r : ℝ)
    (hm : dist w (A^m•z)=r) (hn : dist w (A^n•z)=r) (hk : dist w (A^k•z)=r) :
    A^m•z=A^n•z ∨ A^m•z=A^k•z ∨ A^n•z=A^k•z := by
  have hdist (j : ℤ) (hj : dist w (A^j•z)=r) : dist (q•w) (q•(A^j•z))=r:=by
    rw [(isometry_smul ℍ q).dist_eq]
    exact hj
  have hheight (j : ℤ) : (q•(A^j•z)).im=(q•z).im:=
    realSL_cyclic_conjugate_invariant A q UpperHalfPlane.im hI j z
  have h:=halfPlane_sphere_equal_height_three (q•w) (q•(A^m•z)) (q•(A^n•z)) (q•(A^k•z)) r
    (hdist m hm) (hdist n hn) (hdist k hk) ((hheight n).trans (hheight m).symm)
    ((hheight k).trans (hheight m).symm)
  rcases h with h | h | h
  · exact Or.inl ((isometry_smul ℍ q).injective h)
  · exact Or.inr (Or.inl ((isometry_smul ℍ q).injective h))
  · exact Or.inr (Or.inr ((isometry_smul ℍ q).injective h))

/-- The corresponding statement for genuine cyclic orbits normalized to rays
through the Euclidean origin. -/
theorem realSL_cyclic_circle_of_slope_invariant (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hI : ∀ z : ℍ,((q*A*q⁻¹)•z).re/((q*A*q⁻¹)•z).im=z.re/z.im)
    (z w : ℍ) (m n k : ℤ) (r : ℝ)
    (hm : dist w (A^m•z)=r) (hn : dist w (A^n•z)=r) (hk : dist w (A^k•z)=r) :
    A^m•z=A^n•z ∨ A^m•z=A^k•z ∨ A^n•z=A^k•z := by
  let ρ:=(q•z).re/(q•z).im
  have hdist (j : ℤ) (hj : dist w (A^j•z)=r) : dist (q•w) (q•(A^j•z))=r:=by
    rw [(isometry_smul ℍ q).dist_eq]
    exact hj
  have hslope (j : ℤ) : (q•(A^j•z)).re=ρ*(q•(A^j•z)).im:=by
    have h:=realSL_cyclic_conjugate_invariant A q (fun x=>x.re/x.im) hI j z
    exact (div_eq_iff (q•(A^j•z)).im_ne_zero).mp h
  have h:=halfPlane_sphere_equal_slope_three (q•w) (q•(A^m•z)) (q•(A^n•z)) (q•(A^k•z)) r ρ
    (hdist m hm) (hdist n hn) (hdist k hk) (hslope m) (hslope n) (hslope k)
  rcases h with h | h | h
  · exact Or.inl ((isometry_smul ℍ q).injective h)
  · exact Or.inr (Or.inl ((isometry_smul ℍ q).injective h))
  · exact Or.inr (Or.inr ((isometry_smul ℍ q).injective h))

/-- The geometric circle-intersection obstruction for a genuine parabolic cyclic orbit. -/
theorem realSL_parabolic_cyclic_circle_three (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (z w : ℍ) (m n k : ℤ) (r : ℝ)
    (hm : dist w (A^m•z)=r) (hn : dist w (A^n•z)=r) (hk : dist w (A^k•z)=r) :
    A^m•z=A^n•z ∨ A^m•z=A^k•z ∨ A^n•z=A^k•z := by
  obtain ⟨q,t,_ht,hrot⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  apply realSL_cyclic_circle_of_height_invariant A q _ z w m n k r hm hn hk
  intro u
  rcases hrot with h | h
  · rw [h,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im]
  · have he : (-_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)•u=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•u:=by
      apply UpperHalfPlane.ext
      apply OnePoint.coe_injective
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
    rw [h,he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im]

/-- The geometric circle-intersection obstruction for a genuine hyperbolic cyclic orbit. -/
theorem realSL_hyperbolic_cyclic_circle_three (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2)
    (z w : ℍ) (m n k : ℤ) (r : ℝ)
    (hm : dist w (A^m•z)=r) (hn : dist w (A^n•z)=r) (hk : dist w (A^k•z)=r) :
    A^m•z=A^n•z ∨ A^m•z=A^k•z ∨ A^n•z=A^k•z := by
  obtain ⟨q,t,htpos,_ht1,_hnorm,hact⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_normalizer A hA ht
  apply realSL_cyclic_circle_of_slope_invariant A q _ z w m n k r hm hn hk
  intro u
  rw [hact u]
  have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe t htpos u
  have hre:=congrArg Complex.re he
  have him:=congrArg Complex.im he
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hre
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] at him
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t htpos•u).re=t*u.re at hre
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t htpos•u).im=t*u.im at him
  rw [hre,him]
  exact mul_div_mul_left u.re u.im htpos.ne'

/-- All nonelliptic, nonidentity actual real cyclic orbits obey the true circle obstruction. -/
theorem realSL_nonelliptic_cyclic_circle_three (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hE :
      ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (z w : ℍ) (m n k : ℤ) (r : ℝ)
    (hm : dist w (A^m•z)=r) (hn : dist w (A^n•z)=r) (hk : dist w (A^k•z)=r) :
    A^m•z=A^n•z ∨ A^m•z=A^k•z ∨ A^n•z=A^k•z := by
  have ht : 4≤(Matrix.trace A.val)^2:=by
    by_contra h
    exact hE ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA).mpr (lt_of_not_ge h))
  rcases ht.eq_or_lt with h | h
  · exact realSL_parabolic_cyclic_circle_three A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff A hA).mpr
        h.symm) z w m n k r hm hn hk
  · exact realSL_hyperbolic_cyclic_circle_three A hA h z w m n k r hm hn hk


/-- Literal original sphere-orbit points of an actual cyclic group are realized
by integer powers of the chosen real determinant-one lift. -/
theorem cyclicMobius_orbit_realSL_lift (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hgen : Subgroup.zpowers f=H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A=f) (z x : ℍ)
    (hx : ((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃n : ℤ,x=A^n•z := by
  obtain ⟨g,hg⟩:=hx
  have hmem : g.val∈Subgroup.zpowers f:=by rw [hgen];exact g.property
  obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hmem
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A^n)=g.val:=by rw [map_zpow,hAf,hn]
  refine ⟨n,?_⟩
  symm
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hproj]
  exact hg

/-- The true circle obstruction for the actual original cyclic Mobius action
in a preserved genuine upper half-plane, with no assumed normal form. -/
theorem cyclicMobius_halfPlane_circle_three (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hcyc : IsCyclic H) (hno : ∀ f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (z w x y u : ℍ) (r : ℝ)
    (hx : ((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hy : ((y:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hu : ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hxd : dist w x=r) (hyd : dist w y=r) (hud : dist w u=r) : x=y ∨ x=u ∨ y=u := by
  obtain ⟨f,hgen⟩:=(Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hcyc
  have hfH : f∈H:=by rw [←hgen];exact Subgroup.mem_zpowers f
  obtain ⟨A,hAf⟩:=mobius_preserves_halfPlane_exists_SL f (hpres f hfH)
  obtain ⟨m,rfl⟩:=cyclicMobius_orbit_realSL_lift H f hgen A hAf z x hx
  obtain ⟨n,rfl⟩:=cyclicMobius_orbit_realSL_lift H f hgen A hAf z y hy
  obtain ⟨k,rfl⟩:=cyclicMobius_orbit_realSL_lift H f hgen A hAf z u hu
  by_cases hf : f=1
  · have hfix (j : ℤ) : A^j•z=z:=by
      apply UpperHalfPlane.ext
      apply OnePoint.coe_injective
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,map_zpow,hAf,hf,one_zpow]
      rfl
    exact Or.inl ((hfix m).trans (hfix n).symm)
  · exact realSL_nonelliptic_cyclic_circle_three A (by rwa [hAf])
      (by rw [hAf];exact hno f hfH) z w m n k r hxd hyd hud

/-- The true negative-reciprocal involution is elliptic. -/
theorem circleObstruction_dihedralFlip_elliptic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic fuchsianDihedralFlip := by
  have hn : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal≠1:=by
    intro he
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_infty
    rw [he] at h
    exact OnePoint.coe_ne_infty (0:ℂ) h.symm
  have hfin : IsOfFinOrder _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal:=isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2,by norm_num,by simpa only [pow_two] using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mul_self⟩
  have he:=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal hn hfin
  have h:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal fuchsianQuarterRotation).mpr he
  rwa [fuchsianQuarterRotation_reciprocal] at h

/-- The dihedral branch of the actual elementary Fuchsian classification is
excluded by the original absence of elliptic elements. -/
theorem FuchsianDisc.elementary_noElliptic_isCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (hno : ∀ f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : IsCyclic H := by
  rcases D.elementary_classification he with hc | ⟨q,d,_hdi,_hd,hmodel⟩
  · exact hc
  · have hm : fuchsianDihedralFlip∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H:=by
      rw [hmodel]
      exact Subgroup.subset_closure (by simp only [mem_insert_iff,mem_singleton_iff,or_true])
    obtain ⟨f,hf,hqf⟩:=hm
    have hell : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (q*f*q⁻¹):=by
      change q*f*q⁻¹=fuchsianDihedralFlip at hqf
      rw [hqf]
      exact circleObstruction_dihedralFlip_elliptic
    exact False.elim (hno f hf ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f q).mp hell))


end LowDimensionalTopology.Geometry.Fuchsian
