/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.Subgroup
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfSpaceBall
/-!
# The actual ball stabilizer and Poincaré conjugacy

The equatorial boundary action is recovered from the genuine sphere boundary
homeomorphism. Equatorial chordal distances agree across dimensions, so the
boundary action preserves real cross ratios and belongs to the actual lower-
dimensional reflection group. Uniqueness of the Poincaré extension then
identifies every ball stabilizer with the stated Cayley conjugate.

The final multiplication equivalence has the entire actual ball-preserving
subgroup as its codomain; its underlying action is explicitly conjugation of
the canonical Poincaré extension.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Filter EuclideanGeometry Set
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}


theorem homeomorph_conjugate_preserves_image (h f : Inversive.ExtendedHomeomorph n)
    (S T : Set (Inversive.ExtendedEuclidean n)) (hST : h '' S = T) (hf : f '' S = S) :
    (h*f*h⁻¹) '' T = T := by
  have hi : (h⁻¹ : Inversive.ExtendedHomeomorph n) '' T = S := by rw [← hST,Inversive.homeomorph_inv_image_image]
  change (h ∘ f ∘ (h⁻¹ : Inversive.ExtendedHomeomorph n)) '' T = T
  rw [Set.image_comp,Set.image_comp,hi,hf,hST]

theorem cayleyBall_inverse_image_unitBall :
    ((cayleyBall n)⁻¹ : Inversive.ExtendedHomeomorph (n+1)) '' (Inversive.extendedUnitBall : Set
      (Inversive.ExtendedEuclidean (n+1))) = poincareHalfSpaceSet n 1 := by
  rw [← cayleyBall_image_upperHalfSpace,Inversive.homeomorph_inv_image_image]

theorem cayleyBall_poincare_conjugate_preservesUnitBall [NeZero n] (g : Inversive.GM n) :
    Inversive.PreservesUnitBall (cayleyBall n * (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) * (cayleyBall
      n)⁻¹) :=
  homeomorph_conjugate_preserves_image (cayleyBall n) (poincareExtension g)
    (poincareHalfSpaceSet n 1) Inversive.extendedUnitBall cayleyBall_image_upperHalfSpace
    (poincareExtension_preservesHalfSpaces g 1)

theorem cayleyBall_inverse_conjugate_preservesUpper (f : Inversive.ExtendedHomeomorph (n+1))
    (hB : Inversive.PreservesUnitBall f) :
    ((cayleyBall n)⁻¹*f*cayleyBall n) '' poincareHalfSpaceSet n 1 = poincareHalfSpaceSet n 1 := by
  have he := homeomorph_conjugate_preserves_image (cayleyBall n)⁻¹ f
    Inversive.extendedUnitBall (poincareHalfSpaceSet n 1) cayleyBall_inverse_image_unitBall hB
  simpa only [inv_inv] using he

theorem cayleyBall_equatorial (z : Inversive.ExtendedEuclidean n) :
    cayleyBall n (Inversive.extendedEquatorialEmbedding n z) =
      ((Inversive.stereographicHomeomorph n z).val : Inversive.ExtendedEuclidean (n+1)) := by
  have hP : Inversive.planeReflectionHomeomorph (Inversive.northPole n) 0 (northPole_ne_zero n)
      (Inversive.extendedEquatorialEmbedding n z) = Inversive.extendedEquatorialEmbedding n z := by
    induction z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      change (Inversive.planeReflectionFinite (Inversive.northPole n) 0 (Inversive.equatorialEmbedding n x) :
        Inversive.ExtendedEuclidean (n+1)) =
        (Inversive.equatorialEmbedding n x : Inversive.ExtendedEuclidean (n+1))
      exact congrArg OnePoint.some ((Inversive.planeReflectionFinite_fixed_iff (Inversive.northPole n) 0
        (northPole_ne_zero n) (Inversive.equatorialEmbedding n x)).mpr
        (Inversive.inner_equatorialEmbedding_northPole x))
  change stereographicInversion n
    (Inversive.planeReflectionHomeomorph (Inversive.northPole n) 0 (northPole_ne_zero n)
      (Inversive.extendedEquatorialEmbedding n z)) = _
  rw [hP,stereographicInversion_equatorial]

def boundarySphereHomeomorph (n : ℕ) :
    Inversive.ExtendedEuclidean n ≃ₜ (Inversive.extendedUnitSphere : Set (Inversive.ExtendedEuclidean (n+1))) :=
  (Inversive.stereographicHomeomorph n).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (Metric.sphere (0 : Inversive.Euclidean (n+1)) 1))

theorem boundarySphereHomeomorph_coe (z : Inversive.ExtendedEuclidean n) :
    (boundarySphereHomeomorph n z).val = cayleyBall n (Inversive.extendedEquatorialEmbedding n z) :=
  (cayleyBall_equatorial z).symm

def ballBoundaryAction (f : Inversive.ExtendedHomeomorph (n+1)) (hB : Inversive.PreservesUnitBall
  f) : Inversive.ExtendedHomeomorph n :=
  (boundarySphereHomeomorph n).trans
    ((f.image Inversive.extendedUnitSphere).trans
      ((Homeomorph.setCongr hB.maps_sphere).trans (boundarySphereHomeomorph n).symm))

theorem ballBoundaryAction_transport (f : Inversive.ExtendedHomeomorph (n+1)) (hB : Inversive.PreservesUnitBall f)
    (z : Inversive.ExtendedEuclidean n) :
    cayleyBall n (Inversive.extendedEquatorialEmbedding n (ballBoundaryAction f hB z)) =
      f (cayleyBall n (Inversive.extendedEquatorialEmbedding n z)) := by
  have he : (boundarySphereHomeomorph n (ballBoundaryAction f hB z)).val =
      f (boundarySphereHomeomorph n z).val :=
    congrArg Subtype.val ((boundarySphereHomeomorph n).apply_symm_apply _)
  simpa only [boundarySphereHomeomorph_coe] using he

theorem ballBoundaryAction_extendsBoundary (f : Inversive.ExtendedHomeomorph (n+1)) (hB : Inversive.PreservesUnitBall
  f) :
    ExtendsBoundary (ballBoundaryAction f hB) ((cayleyBall n)⁻¹*f*cayleyBall n) := by
  intro z
  apply (cayleyBall n).injective
  change cayleyBall n ((cayleyBall n).symm (f (cayleyBall n (Inversive.extendedEquatorialEmbedding n z)))) = _
  rw [(cayleyBall n).apply_symm_apply]
  exact (ballBoundaryAction_transport f hB z).symm

theorem chordalDist_equatorialEmbedding (z w : Inversive.ExtendedEuclidean n) :
    Inversive.chordalDist (Inversive.extendedEquatorialEmbedding n z) (Inversive.extendedEquatorialEmbedding n w) =
      Inversive.chordalDist z w := by
  induction z using OnePoint.rec with
  | infty =>
    induction w using OnePoint.rec with
    | infty => simp [Inversive.chordalDist]
    | coe y =>
      rw [Inversive.extendedEquatorialEmbedding_infty,Inversive.extendedEquatorialEmbedding_coe,
        Inversive.chordalDist_infty_coe,Inversive.chordalDist_infty_coe,(Inversive.equatorialEmbedding n).norm_map]
  | coe x =>
    induction w using OnePoint.rec with
    | infty =>
      rw [Inversive.chordalDist_symm,Inversive.chordalDist_symm (x : Inversive.ExtendedEuclidean n) ∞]
      rw [Inversive.extendedEquatorialEmbedding_infty,Inversive.extendedEquatorialEmbedding_coe,
        Inversive.chordalDist_infty_coe,Inversive.chordalDist_infty_coe,(Inversive.equatorialEmbedding n).norm_map]
    | coe y =>
      rw [Inversive.extendedEquatorialEmbedding_coe,Inversive.extendedEquatorialEmbedding_coe,
        Inversive.chordalDist_coe_coe,Inversive.chordalDist_coe_coe,(Inversive.equatorialEmbedding n).norm_map,
        (Inversive.equatorialEmbedding n).norm_map,(Inversive.equatorialEmbedding n).isometry.dist_eq]

theorem realCrossRatio_equatorialEmbedding (x y u v : Inversive.ExtendedEuclidean n) :
    Inversive.realCrossRatio (Inversive.extendedEquatorialEmbedding n x) (Inversive.extendedEquatorialEmbedding n y)
      (Inversive.extendedEquatorialEmbedding n u) (Inversive.extendedEquatorialEmbedding n v) =
        Inversive.realCrossRatio x y u v := by
  simp only [Inversive.realCrossRatio,chordalDist_equatorialEmbedding]

theorem _root_.LowDimensionalTopology.Geometry.Inversive.FourDistinct.equatorialEmbedding {x y u v :
  Inversive.ExtendedEuclidean n} (h : Inversive.FourDistinct x y u v) :
    Inversive.FourDistinct (Inversive.extendedEquatorialEmbedding n x) (Inversive.extendedEquatorialEmbedding n y)
      (Inversive.extendedEquatorialEmbedding n u) (Inversive.extendedEquatorialEmbedding n v) := by
  rcases h with ⟨hxy,hxu,hxv,hyu,hyv,huv⟩
  exact ⟨(Inversive.extendedEquatorialEmbedding_injective n).ne hxy,(Inversive.extendedEquatorialEmbedding_injective
    n).ne hxu,
    (Inversive.extendedEquatorialEmbedding_injective n).ne hxv,(Inversive.extendedEquatorialEmbedding_injective
      n).ne hyu,
    (Inversive.extendedEquatorialEmbedding_injective n).ne hyv,(Inversive.extendedEquatorialEmbedding_injective
      n).ne huv⟩

theorem ballBoundaryAction_preservesRealCrossRatios (f : Inversive.ExtendedHomeomorph (n+1))
    (hf : f ∈ Inversive.generalMobiusGroup (n+1)) (hB : Inversive.PreservesUnitBall f) :
    Inversive.PreservesRealCrossRatios (ballBoundaryAction f hB) := by
  let H := (cayleyBall n)⁻¹*f*cayleyBall n
  have hH : H ∈ Inversive.generalMobiusGroup (n+1) :=
    (Inversive.generalMobiusGroup (n+1)).mul_mem ((Inversive.generalMobiusGroup (n+1)).mul_mem
      ((Inversive.generalMobiusGroup (n+1)).inv_mem (cayleyBall_mem_generalMobiusGroup n)) hf)
      (cayleyBall_mem_generalMobiusGroup n)
  intro x y u v hd
  have he := Inversive.generalMobius_preservesRealCrossRatios H hH
    (Inversive.extendedEquatorialEmbedding n x) (Inversive.extendedEquatorialEmbedding n y)
    (Inversive.extendedEquatorialEmbedding n u) (Inversive.extendedEquatorialEmbedding n v) hd.equatorialEmbedding
  have hE := ballBoundaryAction_extendsBoundary f hB
  change ExtendsBoundary (ballBoundaryAction f hB) H at hE
  rw [hE x,hE y,hE u,hE v,realCrossRatio_equatorialEmbedding,realCrossRatio_equatorialEmbedding] at he
  exact he
theorem ballBoundaryAction_mem_generalMobiusGroup [NeZero n] (f : Inversive.ExtendedHomeomorph (n+1))
    (hf : f ∈ Inversive.generalMobiusGroup (n+1)) (hB : Inversive.PreservesUnitBall f) :
    ballBoundaryAction f hB ∈ Inversive.generalMobiusGroup n := by
  obtain ⟨g,hg,he⟩ := (Inversive.preservesRealCrossRatios_iff_generalMobius
    (ballBoundaryAction f hB : Inversive.ExtendedEuclidean n → Inversive.ExtendedEuclidean n)).mp
      (ballBoundaryAction_preservesRealCrossRatios f hf hB)
  have hEq : g = ballBoundaryAction f hB := by ext z; exact congrFun he z
  exact hEq ▸ hg

/-- Every actual ball stabilizer is a Cayley conjugate of a Poincaré extension. -/
theorem ballPreserver_eq_cayley_poincare [NeZero n] (f : Inversive.ExtendedHomeomorph (n+1))
    (hf : f ∈ Inversive.generalMobiusGroup (n+1)) (hB : Inversive.PreservesUnitBall f) :
    ∃ g : Inversive.GM n, f = cayleyBall n * (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) * (cayleyBall
      n)⁻¹ := by
  let g : Inversive.GM n := ⟨ballBoundaryAction f hB,ballBoundaryAction_mem_generalMobiusGroup f hf hB⟩
  let H := (cayleyBall n)⁻¹*f*cayleyBall n
  have hH : H ∈ Inversive.generalMobiusGroup (n+1) :=
    (Inversive.generalMobiusGroup (n+1)).mul_mem ((Inversive.generalMobiusGroup (n+1)).mul_mem
      ((Inversive.generalMobiusGroup (n+1)).inv_mem (cayleyBall_mem_generalMobiusGroup n)) hf)
      (cayleyBall_mem_generalMobiusGroup n)
  have he : H = poincareExtension g := poincareExtension_unique g H (poincareExtension g) hH
    (poincareExtension g).property (ballBoundaryAction_extendsBoundary f hB)
    (poincareExtension_extendsBoundary g) (cayleyBall_inverse_conjugate_preservesUpper f hB)
    (poincareExtension_preservesHalfSpaces g 1)
  refine ⟨g,?_⟩
  calc
    _ = cayleyBall n*H*(cayleyBall n)⁻¹ := by dsimp only [H]; group
    _ = _ := by rw [he]

theorem cayley_poincare_range_iff [NeZero n] (f : Inversive.ExtendedHomeomorph (n+1)) :
    f ∈ Inversive.generalMobiusGroup (n+1) ∧ Inversive.PreservesUnitBall f ↔
      ∃ g : Inversive.GM n, f = cayleyBall n*(poincareExtension g : Inversive.ExtendedHomeomorph (n+1))*(cayleyBall
        n)⁻¹ := by
  constructor
  · rintro ⟨hf,hB⟩
    exact ballPreserver_eq_cayley_poincare f hf hB
  · rintro ⟨g,rfl⟩
    refine ⟨?_,cayleyBall_poincare_conjugate_preservesUnitBall g⟩
    exact (Inversive.generalMobiusGroup (n+1)).mul_mem ((Inversive.generalMobiusGroup (n+1)).mul_mem
      (cayleyBall_mem_generalMobiusGroup n) (poincareExtension g).property)
      ((Inversive.generalMobiusGroup (n+1)).inv_mem (cayleyBall_mem_generalMobiusGroup n))


def cayleyBallGM (n : ℕ) : Inversive.GM (n+1) := ⟨cayleyBall n,cayleyBall_mem_generalMobiusGroup n⟩

/-- Poincaré extension followed by conjugation, with its genuine ball-stabilizer codomain. -/
def cayleyPoincareHom [NeZero n] : Inversive.GM n →* Inversive.ballPreservingSubgroup n :=
  (((MulAut.conj (cayleyBallGM n)).toMonoidHom).comp (poincareExtensionHom (n := n))).codRestrict
    (Inversive.ballPreservingSubgroup n) (fun g ↦ cayleyBall_poincare_conjugate_preservesUnitBall g)

@[simp] theorem cayleyPoincareHom_coe [NeZero n] (g : Inversive.GM n) :
    ((cayleyPoincareHom g : Inversive.GM (n+1)) : Inversive.ExtendedHomeomorph (n+1)) =
      cayleyBall n*(poincareExtension g : Inversive.ExtendedHomeomorph (n+1))*(cayleyBall n)⁻¹ := rfl

theorem cayleyPoincareHom_injective [NeZero n] : Function.Injective (cayleyPoincareHom (n := n)) := by
  intro g h he
  have hfun := congrArg (fun f : Inversive.ballPreservingSubgroup n ↦ (f.val : Inversive.ExtendedHomeomorph (n+1))) he
  rw [cayleyPoincareHom_coe,cayleyPoincareHom_coe] at hfun
  have hPE : (poincareExtension g : Inversive.ExtendedHomeomorph (n+1)) = poincareExtension h :=
    mul_left_cancel (mul_right_cancel hfun)
  exact poincareExtensionHom_injective (Subtype.ext hPE)

theorem cayleyPoincareHom_surjective [NeZero n] : Function.Surjective (cayleyPoincareHom (n := n)) := by
  intro f
  obtain ⟨g,hg⟩ := ballPreserver_eq_cayley_poincare f.val.val f.val.property f.property
  refine ⟨g,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hg.symm

/-- The full lower-dimensional GM is isomorphic to the actual higher-dimensional ball stabilizer. -/
def cayleyPoincareEquiv [NeZero n] : Inversive.GM n ≃* Inversive.ballPreservingSubgroup n :=
  MulEquiv.ofBijective cayleyPoincareHom ⟨cayleyPoincareHom_injective,cayleyPoincareHom_surjective⟩

@[simp] theorem cayleyPoincareEquiv_coe [NeZero n] (g : Inversive.GM n) :
    ((cayleyPoincareEquiv g : Inversive.GM (n+1)) : Inversive.ExtendedHomeomorph (n+1)) =
      cayleyBall n*(poincareExtension g : Inversive.ExtendedHomeomorph (n+1))*(cayleyBall n)⁻¹ := rfl

end LowDimensionalTopology.Geometry.Hyperbolic
