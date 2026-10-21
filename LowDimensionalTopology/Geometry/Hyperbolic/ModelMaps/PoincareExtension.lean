/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.CrossRatio
public import LowDimensionalTopology.Geometry.Inversive.SpherePointwiseFixer
/-!
# The geometric Poincaré extension

Embedded reflections preserve both signed half-spaces and recover the original
boundary action. In positive boundary dimension uniqueness gives an injective
group homomorphism between the actual general Möbius groups.
The squared Euclidean-distance to height-product quotient is invariant
under every such extension, including all boundary poles.
-/

@[expose] public section
noncomputable section
open scoped OnePoint RealInnerProductSpace
open EuclideanGeometry Set
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

def poincareHalfSpaceSet (n : ℕ) (s : ℝ) : Set (Inversive.ExtendedEuclidean (n+1)) :=
  {z | ∃ x : Inversive.Euclidean (n+1), 0<s*x (Fin.last n) ∧ (x : Inversive.ExtendedEuclidean (n+1))=z}

def PreservesPoincareHalfSpaces (F : Inversive.ExtendedHomeomorph (n+1)) : Prop :=
  ∀ s : ℝ, F '' poincareHalfSpaceSet n s=poincareHalfSpaceSet n s

def ExtendsBoundary (f : Inversive.ExtendedHomeomorph n) (F : Inversive.ExtendedHomeomorph (n+1)) : Prop :=
  ∀ z, F (Inversive.extendedEquatorialEmbedding n z)=Inversive.extendedEquatorialEmbedding n (f z)

theorem poincareHalfSpaceSet_coe (s : ℝ) (x : Inversive.Euclidean (n+1)) :
    (x : Inversive.ExtendedEuclidean (n+1)) ∈ poincareHalfSpaceSet n s ↔ 0<s*x (Fin.last n) := by
  constructor
  · rintro ⟨y,hy,h⟩
    have he := OnePoint.coe_injective h
    simpa only [he] using hy
  · intro hx; exact ⟨x,hx,rfl⟩

theorem poincareHalfSpaceSet_infty (s : ℝ) :
    (∞ : Inversive.ExtendedEuclidean (n+1)) ∉ poincareHalfSpaceSet n s := by
  rintro ⟨x,_,h⟩
  exact OnePoint.coe_ne_infty x h

theorem equatorialEmbedding_ne_zero {a : Inversive.Euclidean n} (ha : a ≠ 0) :
    Inversive.equatorialEmbedding n a ≠ 0 := by
  intro h
  apply ha
  apply (Inversive.equatorialEmbedding n).injective
  simpa only [map_zero] using h

theorem inversion_equatorialEmbedding (c x : Inversive.Euclidean n) (r : ℝ) :
    inversion (Inversive.equatorialEmbedding n c) r (Inversive.equatorialEmbedding n x)=
      Inversive.equatorialEmbedding n (inversion c r x) := by
  rw [Inversive.inversion_formula,Inversive.inversion_formula,map_add,map_smul,
    ←map_sub,(Inversive.equatorialEmbedding n).norm_map]

theorem planeReflectionFinite_equatorialEmbedding (a x : Inversive.Euclidean n) (t : ℝ) :
    Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t (Inversive.equatorialEmbedding n x)=
      Inversive.equatorialEmbedding n (Inversive.planeReflectionFinite a t x) := by
  simp only [Inversive.planeReflectionFinite,map_sub,map_smul,
    (Inversive.equatorialEmbedding n).inner_map_map,(Inversive.equatorialEmbedding n).norm_map]

theorem sphereInversion_extendsBoundary (c : Inversive.Euclidean n) (r : ℝ) (hr : r ≠ 0) :
    ExtendsBoundary (Inversive.sphereInversionHomeomorph c r hr)
      (Inversive.sphereInversionHomeomorph (Inversive.equatorialEmbedding n c) r hr) := by
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    simp only [Inversive.extendedEquatorialEmbedding_coe,Inversive.sphereInversionHomeomorph_apply]
    by_cases hx : x=c
    · subst x
      simp only [Inversive.sphereInversion_center,Inversive.extendedEquatorialEmbedding_infty]
    · rw [Inversive.sphereInversion_coe _ _ ((Inversive.equatorialEmbedding n).injective.ne hx),
        Inversive.sphereInversion_coe _ _ hx,Inversive.extendedEquatorialEmbedding_coe,
        inversion_equatorialEmbedding]

theorem planeReflection_extendsBoundary (a : Inversive.Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    ExtendsBoundary (Inversive.planeReflectionHomeomorph a t ha)
      (Inversive.planeReflectionHomeomorph (Inversive.equatorialEmbedding n a) t (equatorialEmbedding_ne_zero ha)) := by
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    simp only [Inversive.extendedEquatorialEmbedding_coe,Inversive.planeReflectionHomeomorph_apply,
      Inversive.planeReflection_coe,planeReflectionFinite_equatorialEmbedding]

theorem inversion_equatorial_height (c : Inversive.Euclidean n) (r : ℝ) (x : Inversive.Euclidean (n+1)) :
    (inversion (Inversive.equatorialEmbedding n c) r x) (Fin.last n)=
      (r/‖x-Inversive.equatorialEmbedding n c‖)^2*x (Fin.last n) := by
  rw [Inversive.inversion_formula]
  simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,Inversive.equatorialEmbedding_last,
    smul_eq_mul,sub_zero,zero_add]

theorem planeReflection_equatorial_height (a : Inversive.Euclidean n) (t : ℝ)
    (x : Inversive.Euclidean (n+1)) :
    Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t x (Fin.last n)=x (Fin.last n) := by
  simp [Inversive.planeReflectionFinite,PiLp.sub_apply,PiLp.smul_apply,Inversive.equatorialEmbedding_last]

theorem image_poincareHalfSpace_of_involutive (f : Inversive.ExtendedEuclidean (n+1) → Inversive.ExtendedEuclidean
  (n+1))
    (hf : Function.Involutive f) (s : ℝ)
    (hm : MapsTo f (poincareHalfSpaceSet n s) (poincareHalfSpaceSet n s)) :
    f '' poincareHalfSpaceSet n s=poincareHalfSpaceSet n s := by
  apply Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩; exact hm hx
  · intro z hz; exact ⟨f z,hm hz,hf z⟩

theorem sphereInversion_preservesPoincareHalfSpaces (c : Inversive.Euclidean n) (r : ℝ) (hr : 0<r) :
    PreservesPoincareHalfSpaces (Inversive.sphereInversionHomeomorph (Inversive.equatorialEmbedding n c) r hr.ne') := by
  intro s
  apply image_poincareHalfSpace_of_involutive _
    (Inversive.sphereInversion_involutive _ hr.ne')
  rintro z ⟨x,hx,rfl⟩
  have hxc : x ≠ Inversive.equatorialEmbedding n c := by
    intro h; rw [h,Inversive.equatorialEmbedding_last,mul_zero] at hx; exact lt_irrefl _ hx
  change Inversive.sphereInversion (Inversive.equatorialEmbedding n c) r x ∈ _
  rw [Inversive.sphereInversion_coe _ _ hxc,poincareHalfSpaceSet_coe,inversion_equatorial_height]
  have hfactor : 0<(r/‖x-Inversive.equatorialEmbedding n c‖)^2 :=
    sq_pos_of_pos (div_pos hr (norm_pos_iff.mpr (sub_ne_zero.mpr hxc)))
  nlinarith [mul_pos hfactor hx]

theorem planeReflection_preservesPoincareHalfSpaces (a : Inversive.Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    PreservesPoincareHalfSpaces (Inversive.planeReflectionHomeomorph (Inversive.equatorialEmbedding n a) t
      (equatorialEmbedding_ne_zero ha)) := by
  intro s
  apply image_poincareHalfSpace_of_involutive _
    (Inversive.planeReflection_involutive _ t (equatorialEmbedding_ne_zero ha))
  rintro z ⟨x,hx,rfl⟩
  rw [Inversive.planeReflection_coe,poincareHalfSpaceSet_coe,planeReflection_equatorial_height]
  exact hx

theorem ExtendsBoundary.one : ExtendsBoundary (1 : Inversive.ExtendedHomeomorph n) 1 := by
  intro z; rfl

theorem ExtendsBoundary.mul {f g : Inversive.ExtendedHomeomorph n} {F G : Inversive.ExtendedHomeomorph (n+1)}
    (hF : ExtendsBoundary f F) (hG : ExtendsBoundary g G) : ExtendsBoundary (f*g) (F*G) := by
  intro z
  change F (G (Inversive.extendedEquatorialEmbedding n z))=Inversive.extendedEquatorialEmbedding n (f (g z))
  rw [hG z,hF (g z)]

theorem PreservesPoincareHalfSpaces.one : PreservesPoincareHalfSpaces (1 : Inversive.ExtendedHomeomorph (n+1)) := by
  intro s
  exact image_id _

theorem PreservesPoincareHalfSpaces.mul {F G : Inversive.ExtendedHomeomorph (n+1)}
    (hF : PreservesPoincareHalfSpaces F) (hG : PreservesPoincareHalfSpaces G) :
    PreservesPoincareHalfSpaces (F*G) := by
  intro s
  change (fun x => F (G x)) '' poincareHalfSpaceSet n s=poincareHalfSpaceSet n s
  rw [←image_image F G (poincareHalfSpaceSet n s),hG s,hF s]

theorem _root_.LowDimensionalTopology.Geometry.Inversive.IsReflection.exists_poincareExtension {f :
  Inversive.ExtendedHomeomorph n} (hf : Inversive.IsReflection f) :
    ∃ F : Inversive.ExtendedHomeomorph (n+1), Inversive.IsReflection F ∧ ExtendsBoundary f F ∧
      PreservesPoincareHalfSpaces F := by
  rcases hf with ⟨c,r,hr,rfl⟩ | ⟨a,t,ha,rfl⟩
  · exact ⟨Inversive.sphereInversionHomeomorph (Inversive.equatorialEmbedding n c) r hr.ne',
      Inversive.sphereInversion_isReflection _ r hr,sphereInversion_extendsBoundary c r hr.ne',
      sphereInversion_preservesPoincareHalfSpaces c r hr⟩
  · exact ⟨Inversive.planeReflectionHomeomorph (Inversive.equatorialEmbedding n a) t (equatorialEmbedding_ne_zero ha),
      Inversive.planeReflection_isReflection _ t (equatorialEmbedding_ne_zero ha),
      planeReflection_extendsBoundary a t ha,planeReflection_preservesPoincareHalfSpaces a t ha⟩

theorem generalMobius_exists_poincareExtension (f : Inversive.ExtendedHomeomorph n)
    (hf : f ∈ Inversive.generalMobiusGroup n) :
    ∃ F : Inversive.ExtendedHomeomorph (n+1), F ∈ Inversive.generalMobiusGroup (n+1) ∧ ExtendsBoundary f F ∧
      PreservesPoincareHalfSpaces F := by
  obtain ⟨l,hl,rfl⟩ := (Inversive.mem_generalMobiusGroup_iff f).mp hf
  have H : ∀ l : List (Inversive.ExtendedHomeomorph n), (∀ g ∈ l, Inversive.IsReflection g) →
      ∃ F : Inversive.ExtendedHomeomorph (n+1), F ∈ Inversive.generalMobiusGroup (n+1) ∧
        ExtendsBoundary l.prod F ∧ PreservesPoincareHalfSpaces F := by
    intro l
    induction l with
    | nil => intro _; exact ⟨1,(Inversive.generalMobiusGroup (n+1)).one_mem,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.ExtendsBoundary.one,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.PreservesPoincareHalfSpaces.one⟩
    | cons g l ih =>
      intro hl
      obtain ⟨F,hF,hFB,hFH⟩ := (hl g (by simp)).exists_poincareExtension
      obtain ⟨G,hG,hGB,hGH⟩ := ih (fun h hh => hl h (by simp [hh]))
      exact ⟨F*G,(Inversive.generalMobiusGroup (n+1)).mul_mem hF.mem_generalMobiusGroup hG,
        hFB.mul hGB,hFH.mul hGH⟩
  exact H l hl

theorem ExtendsBoundary.inv {f : Inversive.ExtendedHomeomorph n} {F : Inversive.ExtendedHomeomorph (n+1)}
    (hF : ExtendsBoundary f F) : ExtendsBoundary f⁻¹ F⁻¹ := by
  intro z
  apply F.injective
  change F (F.symm (Inversive.extendedEquatorialEmbedding n z))=
    F (Inversive.extendedEquatorialEmbedding n (f.symm z))
  rw [F.apply_symm_apply,hF,f.apply_symm_apply]

theorem poincareExtension_unique [NeZero n] (f : Inversive.ExtendedHomeomorph n)
    (F G : Inversive.ExtendedHomeomorph (n+1)) (hF : F ∈ Inversive.generalMobiusGroup (n+1))
    (hG : G ∈ Inversive.generalMobiusGroup (n+1)) (hFB : ExtendsBoundary f F)
    (hGB : ExtendsBoundary f G)
    (hFH : F '' poincareHalfSpaceSet n 1=poincareHalfSpaceSet n 1)
    (hGH : G '' poincareHalfSpaceSet n 1=poincareHalfSpaceSet n 1) : F=G := by
  have hn : 2≤n+1 := by have h := NeZero.pos n; omega
  have hN : Inversive.northPole n ≠ 0 := norm_ne_zero_iff.mp (by rw [Inversive.norm_northPole]; exact one_ne_zero)
  let D : Inversive.ExtendedHomeomorph (n+1) := G⁻¹*F
  have hD : D ∈ Inversive.generalMobiusGroup (n+1) :=
    (Inversive.generalMobiusGroup (n+1)).mul_mem ((Inversive.generalMobiusGroup (n+1)).inv_mem hG) hF
  have hDE : ExtendsBoundary (1 : Inversive.ExtendedHomeomorph n) D := by
    simpa only [inv_mul_cancel] using hGB.inv.mul hFB
  have hfix (x : Inversive.ExtendedEuclidean (n+1)) (hx : x ∈ Inversive.plane (Inversive.northPole n) 0) : D x=x := by
    rw [←Inversive.extendedEquatorialEmbedding_range n] at hx
    obtain ⟨z,rfl⟩ := hx
    exact hDE z
  rcases Inversive.plane_pointwiseFixer hn D hD (Inversive.northPole n) 0 hN hfix with hd | hd
  · have he : G⁻¹*F=1 := hd
    simpa using congrArg (fun H : Inversive.ExtendedHomeomorph (n+1) => G*H) he
  · exfalso
    let z : Inversive.ExtendedEuclidean (n+1) := Inversive.northPole n
    have hz : z ∈ poincareHalfSpaceSet n 1 := by
      exact ⟨Inversive.northPole n,by simp [Inversive.northPole],rfl⟩
    have hFz : F z ∈ poincareHalfSpaceSet n 1 := by
      rw [←hFH]
      exact ⟨z,hz,rfl⟩
    obtain ⟨y,hy,hGy⟩ : F z ∈ G '' poincareHalfSpaceSet n 1 := by
      rw [hGH]; exact hFz
    have hDy : D z=y := by
      change G.symm (F z)=y
      rw [←hGy,G.symm_apply_apply]
    have hDz : D z ∈ poincareHalfSpaceSet n 1 := hDy.symm ▸ hy
    rw [hd] at hDz
    simp only [Inversive.planeReflectionHomeomorph_apply,z,Inversive.planeReflection_coe,
      poincareHalfSpaceSet_coe] at hDz
    norm_num [Inversive.planeReflectionFinite,real_inner_self_eq_norm_sq,Inversive.norm_northPole,
      PiLp.sub_apply,PiLp.smul_apply,Inversive.northPole] at hDz


def poincareExtension [NeZero n] (g : Inversive.GM n) : Inversive.GM (n+1) :=
  ⟨(generalMobius_exists_poincareExtension (n := n) (g : Inversive.ExtendedHomeomorph n) g.property).choose,
    (generalMobius_exists_poincareExtension (n := n) (g : Inversive.ExtendedHomeomorph n) g.property).choose_spec.1⟩

theorem poincareExtension_extendsBoundary [NeZero n] (g : Inversive.GM n) :
    ExtendsBoundary (n := n) (g : Inversive.ExtendedHomeomorph n)
      (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) :=
  (generalMobius_exists_poincareExtension (n := n) (g : Inversive.ExtendedHomeomorph n) g.property).choose_spec.2.1

theorem poincareExtension_preservesHalfSpaces [NeZero n] (g : Inversive.GM n) :
    PreservesPoincareHalfSpaces (n := n)
      (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) :=
  (generalMobius_exists_poincareExtension (n := n) (g : Inversive.ExtendedHomeomorph n) g.property).choose_spec.2.2

theorem poincareExtension_one [NeZero n] : poincareExtension (1 : Inversive.GM n)=1 := by
  apply Subtype.ext
  exact poincareExtension_unique 1 _ _
    (poincareExtension 1).property (Inversive.generalMobiusGroup (n+1)).one_mem
    (poincareExtension_extendsBoundary 1) _root_.LowDimensionalTopology.Geometry.Hyperbolic.ExtendsBoundary.one
    (poincareExtension_preservesHalfSpaces 1 1) (image_id _)

theorem poincareExtension_mul [NeZero n] (g h : Inversive.GM n) :
    poincareExtension (g*h)=poincareExtension g*poincareExtension h := by
  apply Subtype.ext
  exact poincareExtension_unique (g*h) _ _
    (poincareExtension (g*h)).property
    ((Inversive.generalMobiusGroup (n+1)).mul_mem (poincareExtension g).property (poincareExtension h).property)
    (poincareExtension_extendsBoundary (g*h))
    ((poincareExtension_extendsBoundary g).mul (poincareExtension_extendsBoundary h))
    (poincareExtension_preservesHalfSpaces (g*h) 1)
    (((poincareExtension_preservesHalfSpaces g).mul (poincareExtension_preservesHalfSpaces h)) 1)

def poincareExtensionHom [NeZero n] : Inversive.GM n →* Inversive.GM (n+1) where
  toFun := poincareExtension
  map_one' := poincareExtension_one
  map_mul' := poincareExtension_mul

theorem poincareExtensionHom_injective [NeZero n] :
    Function.Injective (poincareExtensionHom (n := n)) := by
  intro g h he
  apply Subtype.ext
  ext z
  apply Inversive.extendedEquatorialEmbedding_injective n
  have hez := congrArg (fun H : Inversive.GM (n+1) => (H : Inversive.ExtendedHomeomorph (n+1))
    (Inversive.extendedEquatorialEmbedding n z)) he
  change (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) (Inversive.extendedEquatorialEmbedding n z)=
    (poincareExtension h : Inversive.ExtendedHomeomorph (n+1)) (Inversive.extendedEquatorialEmbedding n z) at hez
  rwa [poincareExtension_extendsBoundary g,poincareExtension_extendsBoundary h] at hez


def poincareSeparation (x y : Inversive.Euclidean (n+1)) : ℝ :=
  dist x y^2/(x (Fin.last n)*y (Fin.last n))

theorem sphereInversion_poincareSeparation (c : Inversive.Euclidean n) (r : ℝ) (hr : 0<r)
    (x y : Inversive.Euclidean (n+1)) (hx : 0<x (Fin.last n)) (hy : 0<y (Fin.last n)) :
    poincareSeparation (inversion (Inversive.equatorialEmbedding n c) r x)
      (inversion (Inversive.equatorialEmbedding n c) r y)=poincareSeparation x y := by
  have hxc : x ≠ Inversive.equatorialEmbedding n c := by
    intro h; rw [h,Inversive.equatorialEmbedding_last] at hx; exact lt_irrefl _ hx
  have hyc : y ≠ Inversive.equatorialEmbedding n c := by
    intro h; rw [h,Inversive.equatorialEmbedding_last] at hy; exact lt_irrefl _ hy
  unfold poincareSeparation
  rw [dist_inversion_inversion hxc hyc,inversion_equatorial_height,inversion_equatorial_height]
  simp only [dist_eq_norm]
  field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxc),
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyc),hr.ne',hx.ne',hy.ne']

theorem planeReflection_poincareSeparation (a : Inversive.Euclidean n) (t : ℝ)
    (x y : Inversive.Euclidean (n+1)) :
    poincareSeparation (Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t x)
      (Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t y)=poincareSeparation x y := by
  have hdist : dist (Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t x)
      (Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t y)=dist x y := by
    simpa only [Inversive.planeReflectionFiniteIsometry_apply] using
      (Inversive.planeReflectionFiniteIsometry (Inversive.equatorialEmbedding n a) t).dist_eq x y
  unfold poincareSeparation
  rw [hdist,planeReflection_equatorial_height,planeReflection_equatorial_height]


def PreservesPoincareSeparation (F : Inversive.ExtendedHomeomorph (n+1)) : Prop :=
  ∀ x y : Inversive.Euclidean (n+1), 0<x (Fin.last n) → 0<y (Fin.last n) →
    ∃ X Y : Inversive.Euclidean (n+1), 0<X (Fin.last n) ∧ 0<Y (Fin.last n) ∧
      F x=(X : Inversive.ExtendedEuclidean (n+1)) ∧ F y=(Y : Inversive.ExtendedEuclidean (n+1)) ∧
      poincareSeparation X Y=poincareSeparation x y

theorem PreservesPoincareHalfSpaces.finite_positive {F : Inversive.ExtendedHomeomorph (n+1)}
    (hF : PreservesPoincareHalfSpaces F) (x : Inversive.Euclidean (n+1)) (hx : 0<x (Fin.last n)) :
    ∃ X : Inversive.Euclidean (n+1), 0<X (Fin.last n) ∧ F x=(X : Inversive.ExtendedEuclidean (n+1)) := by
  have hFx : F x ∈ poincareHalfSpaceSet n 1 := by
    rw [←hF 1]
    exact ⟨(x : Inversive.ExtendedEuclidean (n+1)),⟨x,by simpa only [one_mul] using hx,rfl⟩,rfl⟩
  obtain ⟨X,hX,hFX⟩ := hFx
  exact ⟨X,by simpa only [one_mul] using hX,hFX.symm⟩

theorem PreservesPoincareSeparation.one :
    PreservesPoincareSeparation (1 : Inversive.ExtendedHomeomorph (n+1)) := by
  intro x y hx hy
  exact ⟨x,y,hx,hy,rfl,rfl,rfl⟩

theorem PreservesPoincareSeparation.mul {F G : Inversive.ExtendedHomeomorph (n+1)}
    (hF : PreservesPoincareSeparation F) (hG : PreservesPoincareSeparation G) :
    PreservesPoincareSeparation (F*G) := by
  intro x y hx hy
  obtain ⟨X,Y,hX,hY,hGX,hGY,hGq⟩ := hG x y hx hy
  obtain ⟨XX,YY,hXX,hYY,hFX,hFY,hFq⟩ := hF X Y hX hY
  refine ⟨XX,YY,hXX,hYY,?_,?_,hFq.trans hGq⟩
  · change F (G x)=(XX : Inversive.ExtendedEuclidean (n+1)); rw [hGX,hFX]
  · change F (G y)=(YY : Inversive.ExtendedEuclidean (n+1)); rw [hGY,hFY]

theorem sphereInversion_preservesPoincareSeparation (c : Inversive.Euclidean n) (r : ℝ) (hr : 0<r) :
    PreservesPoincareSeparation (Inversive.sphereInversionHomeomorph (Inversive.equatorialEmbedding n c) r hr.ne') := by
  intro x y hx hy
  have hxc : x ≠ Inversive.equatorialEmbedding n c := by
    intro h; rw [h,Inversive.equatorialEmbedding_last] at hx; exact lt_irrefl _ hx
  have hyc : y ≠ Inversive.equatorialEmbedding n c := by
    intro h; rw [h,Inversive.equatorialEmbedding_last] at hy; exact lt_irrefl _ hy
  obtain ⟨X,hX,hFX⟩ := (sphereInversion_preservesPoincareHalfSpaces c r hr).finite_positive x hx
  obtain ⟨Y,hY,hFY⟩ := (sphereInversion_preservesPoincareHalfSpaces c r hr).finite_positive y hy
  refine ⟨X,Y,hX,hY,hFX,hFY,?_⟩
  have heX : X=inversion (Inversive.equatorialEmbedding n c) r x := by
    apply OnePoint.coe_injective
    rw [←hFX,Inversive.sphereInversionHomeomorph_apply,Inversive.sphereInversion_coe _ _ hxc]
  have heY : Y=inversion (Inversive.equatorialEmbedding n c) r y := by
    apply OnePoint.coe_injective
    rw [←hFY,Inversive.sphereInversionHomeomorph_apply,Inversive.sphereInversion_coe _ _ hyc]
  rw [heX,heY]
  exact sphereInversion_poincareSeparation c r hr x y hx hy

theorem planeReflection_preservesPoincareSeparation (a : Inversive.Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    PreservesPoincareSeparation (Inversive.planeReflectionHomeomorph (Inversive.equatorialEmbedding n a) t
      (equatorialEmbedding_ne_zero ha)) := by
  intro x y hx hy
  refine ⟨Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t x,
    Inversive.planeReflectionFinite (Inversive.equatorialEmbedding n a) t y,?_,?_,rfl,rfl,
    planeReflection_poincareSeparation a t x y⟩
  · rwa [planeReflection_equatorial_height]
  · rwa [planeReflection_equatorial_height]

theorem poincareExtension_sphere [NeZero n] (c : Inversive.Euclidean n) (r : ℝ) (hr : 0<r) :
    (poincareExtension (n := n) ⟨Inversive.sphereInversionHomeomorph c r hr.ne',
      (Inversive.sphereInversion_isReflection c r hr).mem_generalMobiusGroup⟩ : Inversive.ExtendedHomeomorph (n+1))=
      Inversive.sphereInversionHomeomorph (Inversive.equatorialEmbedding n c) r hr.ne' := by
  exact poincareExtension_unique _ _ _ (poincareExtension _).property
    (Inversive.sphereInversion_isReflection _ r hr).mem_generalMobiusGroup
    (poincareExtension_extendsBoundary _) (sphereInversion_extendsBoundary c r hr.ne')
    (poincareExtension_preservesHalfSpaces _ 1) (sphereInversion_preservesPoincareHalfSpaces c r hr 1)

theorem poincareExtension_plane [NeZero n] (a : Inversive.Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    (poincareExtension (n := n) ⟨Inversive.planeReflectionHomeomorph a t ha,
      (Inversive.planeReflection_isReflection a t ha).mem_generalMobiusGroup⟩ : Inversive.ExtendedHomeomorph (n+1))=
      Inversive.planeReflectionHomeomorph (Inversive.equatorialEmbedding n a) t (equatorialEmbedding_ne_zero ha) := by
  exact poincareExtension_unique _ _ _ (poincareExtension _).property
    (Inversive.planeReflection_isReflection _ t (equatorialEmbedding_ne_zero ha)).mem_generalMobiusGroup
    (poincareExtension_extendsBoundary _) (planeReflection_extendsBoundary a t ha)
    (poincareExtension_preservesHalfSpaces _ 1) (planeReflection_preservesPoincareHalfSpaces a t ha 1)

theorem _root_.LowDimensionalTopology.Geometry.Inversive.IsReflection.poincareExtension_preservesSeparation [NeZero n]
    {f : Inversive.ExtendedHomeomorph n} (hf : Inversive.IsReflection f) :
    PreservesPoincareSeparation (n := n)
      (poincareExtension (n := n) ⟨f,hf.mem_generalMobiusGroup⟩ : Inversive.ExtendedHomeomorph (n+1)) := by
  rcases hf with ⟨c,r,hr,rfl⟩ | ⟨a,t,ha,rfl⟩
  · rw [poincareExtension_sphere c r hr]
    exact sphereInversion_preservesPoincareSeparation c r hr
  · rw [poincareExtension_plane a t ha]
    exact planeReflection_preservesPoincareSeparation a t ha

theorem poincareExtension_preservesSeparation [NeZero n] (g : Inversive.GM n) :
    PreservesPoincareSeparation (n := n) (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) := by
  have H : ∀ (l : List (Inversive.ExtendedHomeomorph n)) (hl : ∀ f ∈ l, Inversive.IsReflection f),
      PreservesPoincareSeparation (n := n) (poincareExtension (n := n) ⟨l.prod,
        (Inversive.generalMobiusGroup n).list_prod_mem (fun f hf => (hl f hf).mem_generalMobiusGroup)⟩ :
          Inversive.ExtendedHomeomorph (n+1)) := by
    intro l
    induction l with
    | nil =>
      intro hl
      change PreservesPoincareSeparation (n := n) (poincareExtension (1 : Inversive.GM n) : Inversive.ExtendedHomeomorph
        (n+1))
      rw [poincareExtension_one]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.PreservesPoincareSeparation.one
    | cons f l ih =>
      intro hl
      have hf : Inversive.IsReflection f := hl f (by simp)
      have hl' : ∀ h ∈ l, Inversive.IsReflection h := fun h hh => hl h (by simp [hh])
      let gF : Inversive.GM n := ⟨f,hf.mem_generalMobiusGroup⟩
      let gL : Inversive.GM n := ⟨l.prod,(Inversive.generalMobiusGroup n).list_prod_mem
        (fun h hh => (hl' h hh).mem_generalMobiusGroup)⟩
      have heq : (⟨(f::l).prod,(Inversive.generalMobiusGroup n).list_prod_mem
          (fun h hh => (hl h hh).mem_generalMobiusGroup)⟩ : Inversive.GM n)=gF*gL := rfl
      rw [heq,poincareExtension_mul]
      exact hf.poincareExtension_preservesSeparation.mul (ih hl')
  obtain ⟨l,hl,hprod⟩ := (Inversive.mem_generalMobiusGroup_iff (g : Inversive.ExtendedHomeomorph n)).mp g.property
  have heq : g=⟨l.prod,(Inversive.generalMobiusGroup n).list_prod_mem
      (fun f hf => (hl f hf).mem_generalMobiusGroup)⟩ := Subtype.ext hprod.symm
  rw [heq]
  exact H l hl

end LowDimensionalTopology.Geometry.Hyperbolic
