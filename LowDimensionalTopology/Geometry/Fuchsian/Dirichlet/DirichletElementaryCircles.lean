/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletCycleLowerBounds
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Any genuine affine Euclidean line meets an actual hyperbolic circle in
at most two points, using its exact metric conic equation. -/
theorem halfPlane_sphere_affine_height_three (w x y z : ℍ) (r a b : ℝ)
    (hx : dist w x=r) (hy : dist w y=r) (hz : dist w z=r)
    (hRx : x.re=a*x.im+b) (hRy : y.re=a*y.im+b) (hRz : z.re=a*z.im+b) :
    x=y ∨ x=z ∨ y=z := by
  have heq (t : ℍ) (ht : dist w t=r) (hre : t.re=a*t.im+b) :
      (a^2+1)*t.im^2+(2*a*(b-w.re)-2*w.im*Real.cosh r)*t.im+
        ((b-w.re)^2+w.im^2)=0:=by
    have h:=halfPlane_sphere_coordinate_equation w t r ht
    rw [hre] at h
    nlinarith only [h]
  have hA : a^2+1≠0:=ne_of_gt (by positivity)
  rcases quadratic_three_roots (a^2+1) (2*a*(b-w.re)-2*w.im*Real.cosh r) _ x.im y.im z.im hA
    (heq x hx hRx) (heq y hy hRy) (heq z hz hRz) with h|h|h
  · left;apply UpperHalfPlane.ext;apply Complex.ext
    · change x.re=y.re;rw [hRx,hRy,h]
    · exact h
  · right;left;apply UpperHalfPlane.ext;apply Complex.ext
    · change x.re=z.re;rw [hRx,hRz,h]
    · exact h
  · right;right;apply UpperHalfPlane.ext;apply Complex.ext
    · change y.re=z.re;rw [hRy,hRz,h]
    · exact h

/-- Three distinct common points determine the true center of a native
hyperbolic circle; no Euclidean or surrogate distance replaces the metric. -/
theorem halfPlane_two_spheres_three (w u x y z : ℍ) (r s : ℝ)
    (hwx : dist w x=r) (hwy : dist w y=r) (hwz : dist w z=r)
    (hux : dist u x=s) (huy : dist u y=s) (huz : dist u z=s) :
    w=u ∨ x=y ∨ x=z ∨ y=z := by
  let a:=w.re-u.re
  let b:=w.im*Real.cosh r-u.im*Real.cosh s
  let c:=u.re^2+u.im^2-w.re^2-w.im^2
  have hlin (t : ℍ) (hw : dist w t=r) (hu : dist u t=s) :
      2*a*t.re+2*b*t.im+c=0:=by
    have hW:=halfPlane_sphere_coordinate_equation w t r hw
    have hU:=halfPlane_sphere_coordinate_equation u t s hu
    dsimp only [a,b,c]
    nlinarith only [hW,hU]
  by_cases ha : a=0
  · by_cases hb : b=0
    · left
      have hc : c=0:=by have h:=hlin x hwx hux;rw [ha,hb] at h;simpa using h
      have hre : w.re=u.re:=sub_eq_zero.mp ha
      have him : w.im=u.im:=by
        dsimp only [c] at hc
        rw [hre] at hc
        nlinarith only [hc,w.im_pos,u.im_pos]
      exact UpperHalfPlane.ext (Complex.ext hre him)
    · right
      have hh (t : ℍ) (hw : dist w t=r) (hu : dist u t=s) : t.im=x.im:=by
        have ht:=hlin t hw hu
        have hx:=hlin x hwx hux
        rw [ha] at ht hx
        have hp : b*(t.im-x.im)=0:=by nlinarith only [ht,hx]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hb)
      exact halfPlane_sphere_equal_height_three w x y z r hwx hwy hwz
        (hh y hwy huy) (hh z hwz huz)
  · right
    have hh (t : ℍ) (hw : dist w t=r) (hu : dist u t=s) : t.re=(-b/a)*t.im-c/(2*a):=by
      have ht:=hlin t hw hu
      field_simp
      nlinarith only [ht]
    exact halfPlane_sphere_affine_height_three w x y z r (-b/a) (-c/(2*a)) hwx hwy hwz
      (by simpa only [sub_eq_add_neg,neg_div] using hh x hwx hux)
      (by simpa only [sub_eq_add_neg,neg_div] using hh y hwy huy)
      (by simpa only [sub_eq_add_neg,neg_div] using hh z hwz huz)

/-- The entire actual integer orbit of an elliptic native map lies on its
true metric circle about the independently constructed fixed center. -/
theorem elliptic_zpow_orbit_distance (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : (Matrix.trace A.val)^2<4) (z : ℍ) (n : ℤ) :
    dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht) (A^n•z)=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht) z := by
  have hf : A•_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A ht _).mpr rfl
  apply invariant_zpow_smul A (fun p : ℍ=>dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht)
    p) _ n z
  intro p
  calc
    dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht) (A•p)=dist (A•_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht) (A•p):=by rw [hf]
    _=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht) p:=(isometry_smul ℍ A).dist_eq _ _

/-- An actual cyclic native orbit has at most two points on a true circle
whose center is not fixed by the generator, including elliptic generators. -/
theorem realSL_cyclic_circle_three_free_center (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (z w : ℍ) (m n k : ℤ) (r : ℝ) (hfree :
      A•w≠w)
    (hm : dist w (A^m•z)=r) (hn : dist w (A^n•z)=r) (hk : dist w (A^k•z)=r) :
    A^m•z=A^n•z ∨ A^m•z=A^k•z ∨ A^n•z=A^k•z := by
  by_cases he : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  · have ht:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA).mp he
    have hh:=halfPlane_two_spheres_three w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ht) (A^m•z) (A^n•z) (A^k•z)
      r (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht) z) hm hn hk
      (elliptic_zpow_orbit_distance A ht z m) (elliptic_zpow_orbit_distance A ht z n)
      (elliptic_zpow_orbit_distance A ht z k)
    rcases hh with hcenter|hh
    · exact (hfree ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A ht w).mpr hcenter)).elim
    · exact hh
  · exact realSL_nonelliptic_cyclic_circle_three A hA he z w m n k r hm hn hk

/-- The actual original-sphere cyclic circle obstruction only needs the
true circle center to have trivial stabilizer in the original group. -/
theorem cyclicMobius_halfPlane_circle_three_free_center (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hcyc : IsCyclic H) (hpres : ∀f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (z w x y u : ℍ) (r : ℝ)
    (hfree : ∀f∈H,f.val (((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=(((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))→f=1)
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
  · apply realSL_cyclic_circle_three_free_center A (by rwa [hAf]) z w m n k r _ hxd hyd hud
    intro hfix
    apply hf
    apply hfree f hfH
    rw [←hAf,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hfix]

/-- The original native disc circle obstruction holds for cyclic groups
with elliptics as well: the true Dirichlet center has trivial stabilizer. -/
theorem cyclic_circle_three_free_center {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hcyc : IsCyclic H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (z x y u : P.domain.carrier) (r : ℝ)
    (hx : x∈MulAction.orbit H z) (hy : y∈MulAction.orbit H z) (hu : u∈MulAction.orbit H z)
    (hxd : P.hyperbolicDist w x=r) (hyd : P.hyperbolicDist w y=r) (hud : P.hyperbolicDist w u=r) :
    x=y ∨ x=u ∨ y=u := by
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hKcyc : IsCyclic K:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H).isCyclic.mp hcyc
  have hfree : ∀f∈K,f.val (((P.halfPlaneCoordinate
    w:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (((P.halfPlaneCoordinate w:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→f=1:=by
    rintro f ⟨g,hg,rfl⟩ hfix
    rw [←radius_coordinate_sphere P w] at hfix
    change (q*g*q⁻¹)•(q•w.val)=q•w.val at hfix
    have hgfix : g.val w.val=w.val:=q.val.injective (by
      change q•(g•w.val)=q•w.val
      simpa only [mul_smul,inv_smul_smul] using hfix)
    have hg1 : g=1:=congrArg Subtype.val (hw ⟨g,hg⟩ (Subtype.ext hgfix))
    change q*g*q⁻¹=1
    rw [hg1,mul_one,mul_inv_cancel]
  have hh:=cyclicMobius_halfPlane_circle_three_free_center K hKcyc
    (radius_conjugate_preserves_halfPlane P) (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)
    (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate y) (P.halfPlaneCoordinate u) r hfree
    (radius_conjugate_orbit P z x hx) (radius_conjugate_orbit P z y hy)
    (radius_conjugate_orbit P z u hu) hxd hyd hud
  rcases hh with hh|hh|hh
  · exact Or.inl (P.halfPlaneCoordinate.injective hh)
  · exact Or.inr (Or.inl (P.halfPlaneCoordinate.injective hh))
  · exact Or.inr (Or.inr (P.halfPlaneCoordinate.injective hh))

/-- Three actual distinct original orbit points on the Dirichlet circle
exclude the cyclic branch of their original generated subgroup, without
excluding elliptic transformations from the group. -/
theorem radius_pair_not_cyclic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (z : P.domain.carrier) (f g : H) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hf : P.hyperbolicDist w (f•z)=r)
    (hg : P.hyperbolicDist w (g•z)=r)
    (hzf : z≠f•z) (hzg : z≠g•z) (hfg : f•z≠g•z) :
    ¬IsCyclic (Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let K:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH : K≤H:=(Subgroup.closure_le H).2
    (by intro x hx;rcases hx with rfl|rfl;exact f.property;exact g.property)
  let PK:=radius_restrict P K hKH
  have hwK : IsDirichletCenter PK w:=by
    intro k hk
    have heH : (⟨k.val,hKH k.property⟩:H)=1:=hw ⟨k.val,hKH k.property⟩ hk
    have heval : k.val=1:=congrArg (fun u:H=>u.val) heH
    exact Subtype.ext heval
  intro hcyc
  let fK : K:=⟨f.val,Subgroup.subset_closure (by simp)⟩
  let gK : K:=⟨g.val,Subgroup.subset_closure (by simp)⟩
  have hh:=cyclic_circle_three_free_center PK hcyc w hwK z z (f•z) (g•z) r
    ⟨1,one_smul _ _⟩ ⟨fK,rfl⟩ ⟨gK,rfl⟩ hz hf hg
  exact hh.elim hzf (fun h=>h.elim hzg hfg)

/-- An endpoint-pair transformation which does not square to the identity
fixes the two endpoints individually. -/
theorem endpointPair_fix_zero_of_square_ne_one (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer) (hs : f*f≠1) :
    f.val (0:ℂ)=(0:ℂ) := by
  rcases _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_zeroInftyPair_cases ⟨f,hf⟩ with hfix|hexchange
  · exact hfix.1
  · exact (hs (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square f hexchange.1
    hexchange.2)).elim

/-- A two-generator elementary Fuchsian group with neither generator an
involution is cyclic, by the actual endpoint-pair classification. -/
theorem elementary_pair_cyclic_of_square_ne_one {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : H=Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (hf : f*f≠1) (hg : g*g≠1) : IsCyclic H := by
  rcases D.elementary_classification he with hcyc|⟨u,d,_,_,hmodel⟩
  · exact hcyc
  · have hpair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer:=by
      rw [hmodel]
      apply (Subgroup.closure_le _).mpr
      intro k hk
      rcases hk with rfl|rfl
      · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mem_zeroInftyPairStabilizer d
      · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer.mul_mem
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mem_zeroInftyPairStabilizer (-1))
          _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mem_zeroInftyPairStabilizer
    have hs (k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hk : k*k≠1) :
        (u*k*u⁻¹)*(u*k*u⁻¹)≠1:=by
      intro heq
      apply hk
      have heq' : u⁻¹*((u*k*u⁻¹)*(u*k*u⁻¹))*u=k*k:=by group
      rw [heq] at heq'
      simpa only [mul_one,inv_mul_cancel] using heq'.symm
    have hfix (k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hk : k∈H) (hsq : k*k≠1) :
        (u*k*u⁻¹).val (0:ℂ)=(0:ℂ):=
      endpointPair_fix_zero_of_square_ne_one _
        (hpair ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff u H
          _).mpr ⟨k,hk,rfl⟩)) (hs k hsq)
    have hfixf:=hfix f (hH ▸ Subgroup.subset_closure (by simp)) hf
    have hfixg:=hfix g (hH ▸ Subgroup.subset_closure (by simp)) hg
    apply D.conjugate_common_fixed_isCyclic u (0:ℂ)
    have hle : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H≤
        MulAction.stabilizer _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup (((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)):=by
      rw [hH,conjugate_closure_pair]
      apply (Subgroup.closure_le _).mpr
      intro k hk
      rcases hk with rfl|rfl
      · exact hfixf
      · exact hfixg
    exact fun k hk=>hle hk

/-- Three distinct original orbit points on a genuine Dirichlet circle
force an elementary generating pair to contain an actual involution. -/
theorem radius_pair_elementary_involution {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (z : P.domain.carrier) (f g : H) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hf : P.hyperbolicDist w (f•z)=r)
    (hg : P.hyperbolicDist w (g•z)=r)
    (hzf : z≠f•z) (hzg : z≠g•z) (hfg : f•z≠g•z)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    orderOf f.val=2 ∨ orderOf g.val=2 := by
  let K:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH : K≤H:=(Subgroup.closure_le H).2
    (by intro k hk;rcases hk with rfl|rfl;exact f.property;exact g.property)
  have hf1 : f.val≠1:=by intro hh;apply hzf;have hf' : f=1:=Subtype.ext hh;rw [hf',one_smul]
  have hg1 : g.val≠1:=by intro hh;apply hzg;have hg' : g=1:=Subtype.ext hh;rw [hg',one_smul]
  by_cases hs : f.val*f.val=1
  · exact Or.inl (orderOf_eq_prime (by simpa only [pow_two] using hs) hf1)
  · right
    by_contra hgs
    have hg2 : g.val*g.val≠1:=fun hh=>hgs
      (orderOf_eq_prime (by simpa only [pow_two] using hh) hg1)
    exact radius_pair_not_cyclic P w hw z f g r hz hf hg hzf hzg hfg
      (elementary_pair_cyclic_of_square_ne_one (radius_restrict P K hKH).asFuchsianDisc
        f.val g.val rfl he hs hg2)

end LowDimensionalTopology.Geometry.Fuchsian
