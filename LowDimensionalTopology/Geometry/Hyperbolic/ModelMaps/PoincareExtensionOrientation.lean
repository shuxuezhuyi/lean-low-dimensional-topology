/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareExtension
public import LowDimensionalTopology.Geometry.Inversive.Orientation
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyBoundaryGroup

/-!
# Orientation through Poincare extension and Cayley conjugation

Original reflection-word argument supporting the orientation correspondence
. Orientation retains its finite-chart Jacobian definition.
-/

@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n m : ℕ}

theorem generalMobius_conjugation_preservesOrientation_iff [NeZero n]
    (g f : Inversive.ExtendedHomeomorph n) (hg : g∈Inversive.generalMobiusGroup n)
    (hf : f∈Inversive.generalMobiusGroup n) :
    Inversive.PreservesOrientation (g*f*g⁻¹) ↔ Inversive.PreservesOrientation f := by
  obtain ⟨l,hl,hprod⟩:=(Inversive.mem_generalMobiusGroup_iff f).mp hf
  have hc : ∀ h∈l.map (MulAut.conj g),Inversive.IsReflection h := by
    intro h hh
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hh
    exact Inversive.generalMobius_conjugate_isReflection hg (hl r hr)
  have he:=Inversive.reflectionWord_preservesOrientation_iff_even (l.map (MulAut.conj g)) hc
  rw [Inversive.conjugateWord_prod,hprod,List.length_map] at he
  have he':=Inversive.reflectionWord_preservesOrientation_iff_even l hl
  rw [hprod] at he'
  exact he.trans he'.symm

theorem reflectionHom_preservesOrientation_iff [NeZero n] [NeZero m]
    (F : Inversive.GM n →* Inversive.GM m)
    (hF : ∀ g : Inversive.GM n,Inversive.IsReflection (g : Inversive.ExtendedHomeomorph n) →
      Inversive.IsReflection (F g : Inversive.ExtendedHomeomorph m)) (g : Inversive.GM n) :
    Inversive.PreservesOrientation (F g : Inversive.ExtendedHomeomorph m) ↔
      Inversive.PreservesOrientation (g : Inversive.ExtendedHomeomorph n) := by
  obtain ⟨l,hl,hprod⟩:=(Inversive.mem_generalMobiusGroup_iff (g : Inversive.ExtendedHomeomorph n)).mp g.property
  let k : List (Inversive.GM n):=l.attach.map (fun f=>⟨f.val,(hl f.val f.property).mem_generalMobiusGroup⟩)
  have he : k.map (Inversive.generalMobiusGroup n).subtype=l := by
    simp [k,List.map_map]
  have hkp : k.prod=g := by
    apply Subtype.ext
    change (Inversive.generalMobiusGroup n).subtype k.prod=g.val
    rw [map_list_prod,he,hprod]
  have hk : ∀ f∈k,Inversive.IsReflection (f : Inversive.ExtendedHomeomorph n) := by
    intro f hf
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hf
    exact hl r.val r.property
  let H : Inversive.GM n →* Inversive.ExtendedHomeomorph m:=(Inversive.generalMobiusGroup m).subtype.comp F
  have hh : (k.map H).prod=(F g : Inversive.ExtendedHomeomorph m) := by
    rw [← map_list_prod,hkp]
    rfl
  have hR : ∀ f∈k.map H,Inversive.IsReflection f := by
    intro f hf
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hf
    exact hF r (hk r hr)
  have hlen : k.length=l.length := by simp [k]
  have hleft:=Inversive.reflectionWord_preservesOrientation_iff_even (k.map H) hR
  rw [hh,List.length_map,hlen] at hleft
  have hright:=Inversive.reflectionWord_preservesOrientation_iff_even l hl
  rw [hprod] at hright
  exact hleft.trans hright.symm

theorem _root_.LowDimensionalTopology.Geometry.Inversive.IsReflection.poincareExtension_isReflection [NeZero n]
    {f : Inversive.ExtendedHomeomorph n} (hf : Inversive.IsReflection f) :
    Inversive.IsReflection (poincareExtension (n:=n) ⟨f,hf.mem_generalMobiusGroup⟩ :
      Inversive.ExtendedHomeomorph (n+1)) := by
  rcases hf with ⟨c,r,hr,rfl⟩ | ⟨a,t,ha,rfl⟩
  · rw [poincareExtension_sphere c r hr]
    exact Inversive.sphereInversion_isReflection _ r hr
  · rw [poincareExtension_plane a t ha]
    exact Inversive.planeReflection_isReflection _ t (equatorialEmbedding_ne_zero ha)

theorem poincareExtension_preservesOrientation_iff [NeZero n] (g : Inversive.GM n) :
    Inversive.PreservesOrientation (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) ↔
      Inversive.PreservesOrientation (g : Inversive.ExtendedHomeomorph n) := by
  apply reflectionHom_preservesOrientation_iff (poincareExtensionHom (n:=n)) ?_ g
  intro f hf
  exact hf.poincareExtension_isReflection

theorem cayleyPoincareEquiv_preservesOrientation_iff [NeZero n] (g : Inversive.GM n) :
    Inversive.PreservesOrientation ((cayleyPoincareEquiv (n:=n) g).val.val) ↔
      Inversive.PreservesOrientation (g : Inversive.ExtendedHomeomorph n) := by
  change Inversive.PreservesOrientation ((cayleyPoincareHom g).val.val) ↔ _
  rw [cayleyPoincareHom_coe]
  exact (generalMobius_conjugation_preservesOrientation_iff (cayleyBall n)
    (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) (cayleyBall_mem_generalMobiusGroup n)
    (poincareExtension g).property).trans (poincareExtension_preservesOrientation_iff g)

end LowDimensionalTopology.Geometry.Hyperbolic
