/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
@[expose] public section
open Set
open scoped Topology Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
noncomputable section

/-- The original group acts by its genuine isometries in the actual half-plane coordinate. -/
def UnitDiscFuchsianGroup.halfPlaneAction {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) : ℍ ≃ᵢ ℍ where
  toEquiv:=(P.halfPlaneCoordinate.symm.toEquiv.trans (MulAction.toPerm g)).trans P.halfPlaneCoordinate.toEquiv
  isometry_toFun:=by
    apply Isometry.of_dist_eq
    intro x y
    change P.hyperbolicDist (g • P.halfPlaneCoordinate.symm x) (g • P.halfPlaneCoordinate.symm y)=dist x y
    rw [P.hyperbolicDist_smul]
    change dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm x))
      (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm y))=dist x y
    rw [P.halfPlaneCoordinate.apply_symm_apply,P.halfPlaneCoordinate.apply_symm_apply]

theorem UnitDiscFuchsianGroup.halfPlaneAction_apply {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (z : ℍ) :
    P.halfPlaneAction g z=P.halfPlaneCoordinate (g • P.halfPlaneCoordinate.symm z):=rfl

theorem UnitDiscFuchsianGroup.halfPlaneAction_coordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (z : P.domain.carrier) :
    P.halfPlaneAction g (P.halfPlaneCoordinate z)=P.halfPlaneCoordinate (g • z) := by
  rw [P.halfPlaneAction_apply,P.halfPlaneCoordinate.symm_apply_apply]


def UnitDiscFuchsianGroup.halfPlaneActionHom {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : H→*(ℍ ≃ᵢ ℍ) where
  toFun:=P.halfPlaneAction
  map_one':=by
    apply IsometryEquiv.ext
    intro z
    change P.halfPlaneCoordinate ((1 : H) • P.halfPlaneCoordinate.symm z)=z
    rw [one_smul,P.halfPlaneCoordinate.apply_symm_apply]
  map_mul' g h:=by
    apply IsometryEquiv.ext
    intro z
    change P.halfPlaneCoordinate ((g*h) • P.halfPlaneCoordinate.symm z)=
      P.halfPlaneCoordinate (g • P.halfPlaneCoordinate.symm (P.halfPlaneCoordinate (h • P.halfPlaneCoordinate.symm z)))
    rw [P.halfPlaneCoordinate.symm_apply_apply,mul_smul]

theorem UnitDiscFuchsianGroup.halfPlaneActionHom_injective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : Function.Injective P.halfPlaneActionHom := by
  intro g h he
  have hact (z : P.domain.carrier) : g • z=h • z:=by
    have hez:=congrArg (fun f : ℍ ≃ᵢ ℍ=>f (P.halfPlaneCoordinate z)) he
    change P.halfPlaneCoordinate (g • P.halfPlaneCoordinate.symm (P.halfPlaneCoordinate z))=
      P.halfPlaneCoordinate (h • P.halfPlaneCoordinate.symm (P.halfPlaneCoordinate z)) at hez
    rw [P.halfPlaneCoordinate.symm_apply_apply] at hez
    exact P.halfPlaneCoordinate.injective hez
  have hk : h⁻¹*g=1:=P.local_effective (h⁻¹*g)
    ⟨univ,isOpen_univ,⟨P.halfPlaneCoordinate.symm UpperHalfPlane.I,mem_univ _⟩,
      fun z _=>by rw [mul_smul,hact z,inv_smul_smul]⟩
  exact (eq_of_inv_mul_eq_one hk).symm

/-- Distance-defined Dirichlet region for genuine native isometries, including reflected maps. -/
def nativeDirichletDomain (G : Subgroup (ℍ ≃ᵢ ℍ)) (w : ℍ) : Set ℍ:=
  {z | ∀g : G,g≠1→dist z w<dist z (g.val w)}

theorem dirichletDomain_native_image {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) :
    P.halfPlaneCoordinate '' dirichletDomain P w=
      nativeDirichletDomain P.halfPlaneActionHom.range (P.halfPlaneCoordinate w) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩ g hg
    obtain ⟨h,hh⟩:=g.property
    have hn : h≠1:=by
      intro he
      apply hg
      apply Subtype.val_injective
      rw [←hh,he,map_one]
      rfl
    have hc:=hx h hn
    change dist (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate w)<dist (P.halfPlaneCoordinate
      x) (P.halfPlaneCoordinate (h • w)) at hc
    change dist (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate w)<dist (P.halfPlaneCoordinate x) (g.val
      (P.halfPlaneCoordinate w))
    rw [←hh]
    change dist (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate w)<dist (P.halfPlaneCoordinate x) (P.halfPlaneAction h
      (P.halfPlaneCoordinate w))
    rw [P.halfPlaneAction_coordinate]
    exact hc
  · intro hz
    refine ⟨P.halfPlaneCoordinate.symm z,?_,P.halfPlaneCoordinate.apply_symm_apply z⟩
    intro g hg
    have hn : (⟨P.halfPlaneActionHom g,⟨g,rfl⟩⟩ : P.halfPlaneActionHom.range)≠1:=by
      intro he
      apply hg
      apply P.halfPlaneActionHom_injective
      simpa only [map_one,Subgroup.coe_one] using congrArg Subtype.val he
    have hc:=hz ⟨P.halfPlaneActionHom g,⟨g,rfl⟩⟩ hn
    change dist z (P.halfPlaneCoordinate w)<dist z (P.halfPlaneAction g (P.halfPlaneCoordinate w)) at hc
    rw [P.halfPlaneAction_coordinate] at hc
    change dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate w)<
      dist (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) (P.halfPlaneCoordinate (g • w))
    rw [P.halfPlaneCoordinate.apply_symm_apply]
    exact hc


/-- Literal conjugation of actual native isometries, without an orientation restriction. -/
def nativeConjugateGroup (f : ℍ ≃ᵢ ℍ) (G : Subgroup (ℍ ≃ᵢ ℍ)) : Subgroup (ℍ ≃ᵢ ℍ):=
  G.map (MulAut.conj f).toMonoidHom

theorem native_conjugate_apply (f g : ℍ ≃ᵢ ℍ) (z : ℍ) :
    MulAut.conj f g (f z)=f (g z) := by
  change f (g (f.symm (f z)))=f (g z)
  rw [f.symm_apply_apply]

theorem nativeDirichletDomain_conjugate (f : ℍ ≃ᵢ ℍ) (G : Subgroup (ℍ ≃ᵢ ℍ)) (w : ℍ) :
    f '' nativeDirichletDomain G w=nativeDirichletDomain (nativeConjugateGroup f G) (f w) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩ g hg
    obtain ⟨h,hh,hgval⟩:=g.property
    have hne : (⟨h,hh⟩ : G)≠1:=by
      intro he
      apply hg
      apply Subtype.val_injective
      rw [←hgval]
      have hv:=congrArg Subtype.val he
      change h=1 at hv
      rw [hv,map_one]
      rfl
    have hc:=hx ⟨h,hh⟩ hne
    change dist (f x) (f w)<dist (f x) (g.val (f w))
    rw [←hgval]
    change dist (f x) (f w)<dist (f x) (MulAut.conj f h (f w))
    rw [native_conjugate_apply,f.dist_eq,f.dist_eq]
    exact hc
  · intro hz
    refine ⟨f.symm z,?_,f.apply_symm_apply z⟩
    intro g hg
    have hgC : MulAut.conj f g.val∈nativeConjugateGroup f G:=⟨g.val,g.property,rfl⟩
    have hgN : (⟨MulAut.conj f g.val,hgC⟩ : nativeConjugateGroup f G)≠1:=by
      intro he
      apply hg
      apply Subtype.val_injective
      apply (MulAut.conj f).injective
      simpa only [map_one,Subgroup.coe_one] using congrArg Subtype.val he
    have hc:=hz ⟨MulAut.conj f g.val,hgC⟩ hgN
    change dist z (f w)<dist z (MulAut.conj f g.val (f w)) at hc
    rw [native_conjugate_apply] at hc
    rw [←f.dist_eq (f.symm z) w,←f.dist_eq (f.symm z) (g.val w),f.apply_symm_apply]
    exact hc

/-- The actual original domain obeys the full any-isometry conjugation formula. -/
theorem dirichletDomain_isometry_conjugate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (f : ℍ ≃ᵢ ℍ) :
    f '' (P.halfPlaneCoordinate '' dirichletDomain P w)=
      nativeDirichletDomain (nativeConjugateGroup f P.halfPlaneActionHom.range) (f (P.halfPlaneCoordinate w)) := by
  rw [dirichletDomain_native_image,nativeDirichletDomain_conjugate]

theorem native_bisector_conjugate (f g : ℍ ≃ᵢ ℍ) (w : ℍ) :
    f '' {z | dist z w=dist z (g w)}=
      {z | dist z (f w)=dist z (MulAut.conj f g (f w))} := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change dist (f x) (f w)=dist (f x) (MulAut.conj f g (f w))
    rw [native_conjugate_apply,f.dist_eq,f.dist_eq]
    exact hx
  · intro hz
    refine ⟨f.symm z,?_,f.apply_symm_apply z⟩
    change dist z (f w)=dist z (MulAut.conj f g (f w)) at hz
    rw [native_conjugate_apply] at hz
    change dist (f.symm z) w=dist (f.symm z) (g w)
    rw [←f.dist_eq (f.symm z) w,←f.dist_eq (f.symm z) (g w),f.apply_symm_apply]
    exact hz

theorem native_halfPlane_conjugate (f g : ℍ ≃ᵢ ℍ) (w : ℍ) :
    f '' {z | dist z w<dist z (g w)}=
      {z | dist z (f w)<dist z (MulAut.conj f g (f w))} := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change dist (f x) (f w)<dist (f x) (MulAut.conj f g (f w))
    rw [native_conjugate_apply,f.dist_eq,f.dist_eq]
    exact hx
  · intro hz
    refine ⟨f.symm z,?_,f.apply_symm_apply z⟩
    change dist z (f w)<dist z (MulAut.conj f g (f w)) at hz
    rw [native_conjugate_apply] at hz
    change dist (f.symm z) w<dist (f.symm z) (g w)
    rw [←f.dist_eq (f.symm z) w,←f.dist_eq (f.symm z) (g w),f.apply_symm_apply]
    exact hz

theorem dirichletDomain_group_center_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) :
    g • dirichletDomain P w=dirichletDomain P (g • w) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩ h hh
    have hn : g⁻¹*h*g≠1:=by
      intro he
      apply hh
      have hv:=congrArg (fun k : H=>g*k*g⁻¹) he
      simpa [mul_assoc] using hv
    have hc:=hx (g⁻¹*h*g) hn
    change P.hyperbolicDist (g • x) (g • w)<P.hyperbolicDist (g • x) (h • (g • w))
    have hr : P.hyperbolicDist (g • x) (h • (g • w))=
        P.hyperbolicDist x ((g⁻¹*h*g) • w):=by
      rw [←P.hyperbolicDist_smul g⁻¹ (g • x) (h • (g • w)),inv_smul_smul]
      simp only [mul_smul]
    rw [P.hyperbolicDist_smul,hr]
    exact hc
  · intro hz
    refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
    intro h hh
    have hn : g*h*g⁻¹≠1:=by
      intro he
      apply hh
      have hv:=congrArg (fun k : H=>g⁻¹*k*g) he
      simpa [mul_assoc] using hv
    have hc:=hz (g*h*g⁻¹) hn
    change P.hyperbolicDist z (g • w)<P.hyperbolicDist z ((g*h*g⁻¹) • (g • w)) at hc
    rw [P.hyperbolicDist_inverse_smul] at hc
    change P.hyperbolicDist (g⁻¹ • z) w<P.hyperbolicDist (g⁻¹ • z) (h • w)
    rw [←P.hyperbolicDist_smul g (g⁻¹ • z) (h • w),smul_inv_smul]
    simpa only [mul_smul,inv_smul_smul] using hc


theorem dirichletBisector_isometry_conjugate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (f : ℍ ≃ᵢ ℍ) :
    f '' (P.halfPlaneCoordinate '' dirichletBisector P w g)=
      {z | dist z (f (P.halfPlaneCoordinate w))=
        dist z (MulAut.conj f (P.halfPlaneAction g) (f (P.halfPlaneCoordinate w)))} := by
  rw [dirichletBisector_halfPlane_image]
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus (P.halfPlaneCoordinate
    w) (P.halfPlaneCoordinate (g • w))=
      {z | dist z (P.halfPlaneCoordinate w)=dist z (P.halfPlaneAction g (P.halfPlaneCoordinate w))}:=by
    rw [P.halfPlaneAction_coordinate]
    rfl
  rw [he,native_bisector_conjugate]

theorem dirichletHalfPlane_isometry_conjugate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (f : ℍ ≃ᵢ ℍ) :
    f '' (P.halfPlaneCoordinate '' dirichletHalfPlane P w g)=
      {z | dist z (f (P.halfPlaneCoordinate w))<
        dist z (MulAut.conj f (P.halfPlaneAction g) (f (P.halfPlaneCoordinate w)))} := by
  rw [dirichletHalfPlane_halfPlane_image]
  have he : {z : ℍ | dist z (P.halfPlaneCoordinate w)<dist z (P.halfPlaneCoordinate (g • w))}=
      {z | dist z (P.halfPlaneCoordinate w)<dist z (P.halfPlaneAction g (P.halfPlaneCoordinate w))}:=by
    rw [P.halfPlaneAction_coordinate]
  rw [he,native_halfPlane_conjugate]

end
end LowDimensionalTopology.Geometry.Fuchsian
