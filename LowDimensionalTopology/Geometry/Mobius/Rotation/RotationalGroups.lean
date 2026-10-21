/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.HyperbolicExtension
/-!
# Finite rotation groups and their unitary binary covers

Cayley conjugation turns every origin plane reflection into an embedded
boundary reflection. Reflection words therefore lift actual orthogonal
three-space actions with the same orientation. Every orientation-preserving
rotation has a faithful Mobius realization; finite rotation groups give finite
Mobius subgroups and finite determinant-one unitary inverse images.
-/

@[expose] public section
noncomputable section
open scoped OnePoint RealInnerProductSpace
open Set
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius

/-- The native upper-half-space boundary is the full equatorial plane, including infinity. -/
theorem frontier_native_upperHalfSpace :
    frontier (Hyperbolic.poincareHalfSpaceSet 2 1) = Inversive.plane (Inversive.northPole 2) 0 := by
  rw [← quaternionChart_preimage_halfSpace, ←
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.preimage_frontier,
    Hyperbolic.QuaternionHalfSpace.frontier_extendedUpperHalfSpaceSet]
  ext x
  induction x using OnePoint.rec with
  | infty => simp [Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion, Inversive.plane]
  | coe x =>
    change ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈
      insert ∞ (((↑) : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace → OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ''
        (Hyperbolic.QuaternionHalfSpace.quaternionBoundarySpace : Set
          Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace))) ↔ _
    simp [Inversive.plane, Hyperbolic.QuaternionHalfSpace.quaternionBoundarySpace, Inversive.northPole,
      EuclideanSpace.inner_single_right]
    change Hyperbolic.QuaternionHalfSpace.quaternionHeight
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x) = 0 ↔ x 2 = 0
    rfl

/-- Every homeomorphism preserving H3 preserves its whole boundary plane. -/
theorem preservesNativeBoundary_of_preservesHalfSpace (F : Inversive.ExtendedHomeomorph 3)
    (hF : F '' Hyperbolic.poincareHalfSpaceSet 2 1 = Hyperbolic.poincareHalfSpaceSet 2 1) :
    F '' Inversive.plane (Inversive.northPole 2) 0 = Inversive.plane (Inversive.northPole 2) 0 := by
  rw [← frontier_native_upperHalfSpace, F.image_frontier, hF]

/-- Native finite boundary membership is exactly zero last coordinate. -/
theorem mem_native_boundary_iff (x : Inversive.Euclidean 3) :
    (x : Inversive.ExtendedEuclidean 3) ∈ Inversive.plane (Inversive.northPole 2) 0 ↔ x (Fin.last 2) = 0 := by
  simp [Inversive.plane, Inversive.northPole, EuclideanSpace.inner_single_right]

/-- A sphere inversion preserving H3 has its centre in the boundary plane. -/
theorem sphereHalfSpace_centre_zero_height (c : Inversive.Euclidean 3) (r : ℝ) (hr : r ≠ 0)
    (hH : Inversive.sphereInversionHomeomorph c r hr '' Hyperbolic.poincareHalfSpaceSet 2 1 =
      Hyperbolic.poincareHalfSpaceSet 2 1) : c (Fin.last 2) = 0 := by
  have hb := preservesNativeBoundary_of_preservesHalfSpace _ hH
  have hi : (∞ : Inversive.ExtendedEuclidean 3) ∈ Inversive.plane (Inversive.northPole 2) 0 := by simp [Inversive.plane]
  have hc : Inversive.sphereInversionHomeomorph c r hr ∞ ∈ Inversive.plane (Inversive.northPole 2) 0 := by
    rw [← hb]
    exact ⟨∞, hi, rfl⟩
  rw [Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_infty, mem_native_boundary_iff] at hc
  exact hc

/-- A genuine plane reflection preserving H3 has horizontal normal. -/
theorem planeHalfSpace_normal_zero_height (a : Inversive.Euclidean 3) (t : ℝ) (ha : a ≠ 0)
    (hH : Inversive.planeReflectionHomeomorph a t ha '' Hyperbolic.poincareHalfSpaceSet 2 1 =
      Hyperbolic.poincareHalfSpaceSet 2 1) : a (Fin.last 2) = 0 := by
  have hb := preservesNativeBoundary_of_preservesHalfSpace _ hH
  have hmap (x : Inversive.Euclidean 3) (hx : x (Fin.last 2) = 0) :
      Inversive.planeReflectionFinite a t x (Fin.last 2) = 0 := by
    have hm : Inversive.planeReflectionHomeomorph a t ha (x : Inversive.ExtendedEuclidean 3) ∈
        Inversive.plane (Inversive.northPole 2) 0 := by
      rw [← hb]
      exact ⟨x, (mem_native_boundary_iff x).mpr hx, rfl⟩
    rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe, mem_native_boundary_iff] at hm
    exact hm
  by_contra hz
  have hn : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  have ht : t = 0 := by
    have h0 := hmap 0 (by simp)
    simp [Inversive.planeReflectionFinite] at h0
    rcases h0 with (h0 | h0) | h0
    · exact h0
    · exact (ha h0).elim
    · exact (hz h0).elim
  have hcoord (i : Fin 2) : a i.castSucc = 0 := by
    have hilast : (2 : Fin 3) ≠ i.castSucc := by
      simpa only [show (Fin.last 2 : Fin 3) = 2 from rfl] using (Fin.castSucc_ne_last i).symm
    have hi := hmap (EuclideanSpace.single i.castSucc 1) (by simpa using hilast)
    rw [ht] at hi
    simp [Inversive.planeReflectionFinite, EuclideanSpace.inner_single_left, hilast] at hi
    rcases hi with (hi | hi) | hi
    · exact hi
    · exact (ha hi).elim
    · exact (hz hi).elim
  have hnorm : ‖a‖ ^ 2 = (a (Fin.last 2)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    have h0 := hcoord 0
    have h1 := hcoord 1
    simp [show a 0 = 0 from h0, show a 1 = 0 from h1]
  have hp : (Inversive.northPole 2 : Inversive.ExtendedEuclidean 3) ∈ Hyperbolic.poincareHalfSpaceSet 2 1 := by
    rw [Hyperbolic.poincareHalfSpaceSet_coe]
    simp [Inversive.northPole]
  have hneg : Inversive.planeReflectionHomeomorph a t ha (Inversive.northPole 2 : Inversive.ExtendedEuclidean 3) ∈
      Hyperbolic.poincareHalfSpaceSet 2 1 := by
    rw [← hH]
    exact ⟨Inversive.northPole 2, hp, rfl⟩
  rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe,
    Hyperbolic.poincareHalfSpaceSet_coe, ht] at hneg
  simp [Inversive.planeReflectionFinite, Inversive.northPole, EuclideanSpace.inner_single_left, hnorm] at hneg
  have he : 2 * a 2 / a 2 ^ 2 * a 2 = 2 := by
    have hz2 : a 2 ≠ 0 := hz
    field_simp [hz2]
  rw [he] at hneg
  linarith


/-- Every genuine reflection preserving H3 is an embedded real-plane reflection. -/
theorem reflectionHalfSpace_boundaryReflection {R : Inversive.ExtendedHomeomorph 3}
    (hR : Inversive.IsReflection R) (hH : R '' Hyperbolic.poincareHalfSpaceSet 2 1 =
      Hyperbolic.poincareHalfSpaceSet 2 1) :
    ∃ f : Inversive.ExtendedHomeomorph 2, Inversive.IsReflection f ∧ Hyperbolic.ExtendsBoundary f R := by
  rcases hR with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · have hc := sphereHalfSpace_centre_zero_height c r hr.ne' hH
    have hcRange : c ∈ Set.range (Inversive.equatorialEmbedding 2) := by
      rw [Inversive.equatorialEmbedding_range]
      exact hc
    obtain ⟨c₀, rfl⟩ := hcRange
    exact ⟨Inversive.sphereInversionHomeomorph c₀ r hr.ne', Inversive.sphereInversion_isReflection c₀ r hr,
      Hyperbolic.sphereInversion_extendsBoundary c₀ r hr.ne'⟩
  · have haHeight := planeHalfSpace_normal_zero_height a t ha hH
    have haRange : a ∈ Set.range (Inversive.equatorialEmbedding 2) := by
      rw [Inversive.equatorialEmbedding_range]
      exact haHeight
    obtain ⟨a₀, rfl⟩ := haRange
    have ha₀ : a₀ ≠ 0 := by intro h; simp [h] at ha
    exact ⟨Inversive.planeReflectionHomeomorph a₀ t ha₀, Inversive.planeReflection_isReflection a₀ t ha₀,
      Hyperbolic.planeReflection_extendsBoundary a₀ t ha₀⟩

/-- Such a reflection is exactly the canonical geometric extension of its boundary reflection. -/
theorem reflectionHalfSpace_poincareExtension {R : Inversive.ExtendedHomeomorph 3}
    (hR : Inversive.IsReflection R) (hH : R '' Hyperbolic.poincareHalfSpaceSet 2 1 =
      Hyperbolic.poincareHalfSpaceSet 2 1) :
    ∃ f : Inversive.GM 2, Inversive.IsReflection (f : Inversive.ExtendedHomeomorph 2) ∧
      (Hyperbolic.poincareExtension f : Inversive.ExtendedHomeomorph 3) = R := by
  obtain ⟨f, hf, hB⟩ := reflectionHalfSpace_boundaryReflection hR hH
  refine ⟨⟨f, hf.mem_generalMobiusGroup⟩, hf, ?_⟩
  apply Hyperbolic.poincareExtension_unique f _ _ (Hyperbolic.poincareExtension _).property
    hR.mem_generalMobiusGroup (Hyperbolic.poincareExtension_extendsBoundary _) hB
    (Hyperbolic.poincareExtension_preservesHalfSpaces _ 1) hH

/-- Pull back a true ball symmetry through the actual Cayley transformation. -/
def cayleyPullback (F : Inversive.ExtendedHomeomorph 3) : Inversive.ExtendedHomeomorph 3 :=
  cayleyEuclideanHomeomorph⁻¹ * F * cayleyEuclideanHomeomorph

theorem cayleyPullback_preservesHalfSpace (F : Inversive.ExtendedHomeomorph 3)
    (hB : Inversive.PreservesUnitBall F) :
    cayleyPullback F '' Hyperbolic.poincareHalfSpaceSet 2 1 = Hyperbolic.poincareHalfSpaceSet 2 1 := by
  change (cayleyEuclideanHomeomorph.symm ∘ F ∘ cayleyEuclideanHomeomorph) ''
    Hyperbolic.poincareHalfSpaceSet 2 1 = _
  calc
    _ = cayleyEuclideanHomeomorph.symm ''
        (F '' (cayleyEuclideanHomeomorph '' Hyperbolic.poincareHalfSpaceSet 2 1)) := by
      rw [Set.image_image, Set.image_image]
      rfl
    _ = _ := by
      rw [cayleyEuclideanHomeomorph_image_halfSpace, hB,
        cayleyEuclideanHomeomorph.symm.image_eq_preimage_symm]
      exact cayleyEuclideanHomeomorph_preimage_ball.symm

/-- Each orthogonal plane reflection of the ball has a genuine boundary reflection lift. -/
theorem ballPlaneReflection_exists_boundary (a : Inversive.Euclidean 3) (ha : a ≠ 0) :
    ∃ f : Inversive.GM 2, Inversive.IsReflection (f : Inversive.ExtendedHomeomorph 2) ∧
      (Hyperbolic.poincareExtension f : Inversive.ExtendedHomeomorph 3) =
        cayleyPullback (Inversive.planeReflectionHomeomorph a 0 ha) := by
  have hR : Inversive.IsReflection (cayleyPullback (Inversive.planeReflectionHomeomorph a 0 ha)) := by
    unfold cayleyPullback
    exact Inversive.generalMobius_conjugate_isReflection
      ((Inversive.generalMobiusGroup 3).inv_mem cayleyEuclideanHomeomorph_mem_generalMobiusGroup)
      (Inversive.planeReflection_isReflection a 0 ha)
  exact reflectionHalfSpace_poincareExtension hR
    (cayleyPullback_preservesHalfSpace _ (Inversive.planeReflection_preservesUnitBall_zero a ha))


/-- Conjugation is used as a genuine group homomorphism, including finite reflection words. -/
def cayleyPullbackHom : Inversive.ExtendedHomeomorph 3 →* Inversive.ExtendedHomeomorph 3 where
  toFun := cayleyPullback
  map_one' := by simp [cayleyPullback]
  map_mul' F G := by dsimp [cayleyPullback]; group

/-- Lift an entire orthogonal-reflection word without changing its length or parity. -/
theorem ballPlaneReflectionWord_boundary (l : List (Inversive.ExtendedHomeomorph 3))
    (hl : ∀ R ∈ l, ∃ a : Inversive.Euclidean 3, ∃ ha : a ≠ 0, R = Inversive.planeReflectionHomeomorph a 0 ha) :
    ∃ k : List (Inversive.GM 2), k.length = l.length ∧
      (∀ f ∈ k, Inversive.IsReflection (f : Inversive.ExtendedHomeomorph 2)) ∧
      (Hyperbolic.poincareExtension k.prod : Inversive.ExtendedHomeomorph 3) = cayleyPullbackHom l.prod := by
  induction l with
  | nil =>
    refine ⟨[], rfl, by simp, ?_⟩
    rw [List.prod_nil, List.prod_nil, Hyperbolic.poincareExtension_one, map_one]
    rfl
  | cons R l ih =>
    obtain ⟨a, ha, rfl⟩ := hl R (by simp)
    obtain ⟨g, hg, he⟩ := ballPlaneReflection_exists_boundary a ha
    obtain ⟨k, hk, hkr, hke⟩ := ih (fun S hS => hl S (List.mem_cons_of_mem _ hS))
    refine ⟨g :: k, by simpa only [List.length_cons] using congrArg Nat.succ hk, ?_, ?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hg
      · exact hkr f hf
    · rw [List.prod_cons, List.prod_cons, Hyperbolic.poincareExtension_mul, Subgroup.coe_mul, he, hke,
        map_mul]
      rfl

/-- All orthogonal ball maps have a genuine boundary Mobius lift with the same orientation. -/
theorem orthogonal_ball_boundary (L : Inversive.Euclidean 3 ≃ₗᵢ[ℝ] Inversive.Euclidean 3) :
    ∃ f : Inversive.GM 2,
      (Hyperbolic.poincareExtension f : Inversive.ExtendedHomeomorph 3) = cayleyPullback
        (Inversive.cartanLinearExtensionHom L) ∧
      (Inversive.PreservesOrientation (f : Inversive.ExtendedHomeomorph 2) ↔
        Inversive.PreservesOrientation (Inversive.cartanLinearExtensionHom L)) := by
  obtain ⟨l, _, hl, hprod⟩ := Inversive.cartanLinearExtension_reflections L
  obtain ⟨k, hk, hkr, hke⟩ := ballPlaneReflectionWord_boundary l hl
  refine ⟨k.prod, ?_, ?_⟩
  · rw [hke, hprod]
    rfl
  · have hkp : (k.map (fun f : Inversive.GM 2 => (f : Inversive.ExtendedHomeomorph 2))).prod =
        (k.prod : Inversive.ExtendedHomeomorph 2) := by
      clear hk hkr hke
      induction k with
      | nil => rfl
      | cons f k ih =>
        simpa only [List.map_cons, List.prod_cons, Subgroup.coe_mul] using
          (congrArg (fun F : Inversive.ExtendedHomeomorph 2 => (f : Inversive.ExtendedHomeomorph 2) * F) ih)
    have hkm : ∀ f ∈ k.map (fun f : Inversive.GM 2 => (f : Inversive.ExtendedHomeomorph 2)),
      Inversive.IsReflection f := by
      intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact hkr g hg
    have hlr : ∀ R ∈ l, Inversive.IsReflection R := by
      intro R hR
      obtain ⟨a, ha, rfl⟩ := hl R hR
      exact Inversive.planeReflection_isReflection a 0 ha
    rw [← hkp, Inversive.reflectionWord_preservesOrientation_iff_even _ hkm, List.length_map, hk,
      ← Inversive.reflectionWord_preservesOrientation_iff_even l hlr, hprod]
    rfl

/-- Every orientation-preserving Euclidean ball rotation is realized by the actual Mobius group. -/
theorem rotation_exists_mobius (L : Inversive.Euclidean 3 ≃ₗᵢ[ℝ] Inversive.Euclidean 3)
    (hL : Inversive.PreservesOrientation (Inversive.cartanLinearExtensionHom L)) :
    ∃ f : complexMobiusGroup, mobiusBallConjugate f = Inversive.cartanLinearExtensionHom L := by
  obtain ⟨g, hg, hgo⟩ := orthogonal_ball_boundary L
  have hgm : euclideanToComplexHom (g : Inversive.ExtendedHomeomorph 2) ∈ complexMobiusGroup :=
    (mem_complexMobiusGroup_iff_real _).mpr ⟨g, g.property, hgo.mpr hL, rfl⟩
  let f : complexMobiusGroup := ⟨euclideanToComplexHom g, hgm⟩
  refine ⟨f, ?_⟩
  have hr : mobiusRealRepresentative f = g := by
    apply Subtype.ext
    apply euclideanToComplexHom_injective
    rw [mobiusRealRepresentative_coordinates]
  change cayleyEuclideanHomeomorph *
    (Hyperbolic.poincareExtension (mobiusRealRepresentative f) : Inversive.ExtendedHomeomorph 3) *
      cayleyEuclideanHomeomorph⁻¹ = _
  rw [hr, hg]
  unfold cayleyPullback
  group


/-- The global ball conjugate is a faithful group representation. -/
def mobiusBallConjugateHom : complexMobiusGroup →* Inversive.ExtendedHomeomorph 3 :=
  (MulAut.conj cayleyEuclideanHomeomorph).toMonoidHom.comp
    ((Inversive.generalMobiusGroup 3).subtype.comp mobiusGeometricPoincareHom)

@[simp] theorem mobiusBallConjugateHom_apply (f : complexMobiusGroup) :
    mobiusBallConjugateHom f = mobiusBallConjugate f := rfl

theorem mobiusBallConjugateHom_injective : Function.Injective mobiusBallConjugateHom := by
  intro f g h
  apply mobiusGeometricPoincareHom_injective
  apply Subtype.ext
  exact (MulAut.conj cayleyEuclideanHomeomorph).injective h

/-- Actual orientation-preserving orthogonal transformations of Euclidean three-space. -/
def rotationGroupThree : Subgroup (Inversive.Euclidean 3 ≃ₗᵢ[ℝ] Inversive.Euclidean 3) :=
  (Inversive.orientationPreservingMobiusGroup 3).comap Inversive.cartanLinearExtensionHom

/-- The unique Mobius realization of an actual rotation. -/
def rotationMobius (g : rotationGroupThree) : complexMobiusGroup :=
  Classical.choose (rotation_exists_mobius g.val g.property.2)

theorem rotationMobius_ball (g : rotationGroupThree) :
    mobiusBallConjugate (rotationMobius g) = Inversive.cartanLinearExtensionHom g.val :=
  Classical.choose_spec (rotation_exists_mobius g.val g.property.2)

/-- The realization preserves all group operations, rather than choosing unrelated representatives. -/
def rotationMobiusHom : rotationGroupThree →* complexMobiusGroup where
  toFun := rotationMobius
  map_one' := by
    apply mobiusBallConjugateHom_injective
    rw [mobiusBallConjugateHom_apply, rotationMobius_ball, map_one,
      Subgroup.coe_one, map_one]
  map_mul' g h := by
    apply mobiusBallConjugateHom_injective
    rw [map_mul, mobiusBallConjugateHom_apply, mobiusBallConjugateHom_apply,
      mobiusBallConjugateHom_apply, rotationMobius_ball, rotationMobius_ball, rotationMobius_ball]
    exact Inversive.cartanLinearExtensionHom.map_mul _ _

theorem rotationMobiusHom_injective : Function.Injective rotationMobiusHom := by
  intro g h he
  have hb := congrArg mobiusBallConjugateHom he
  change mobiusBallConjugate (rotationMobius g) = mobiusBallConjugate (rotationMobius h) at hb
  rw [rotationMobius_ball, rotationMobius_ball] at hb
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  have hx := congrArg (fun F : Inversive.ExtendedHomeomorph 3 => F (x : Inversive.ExtendedEuclidean 3)) hb
  exact OnePoint.coe_injective hx

/-- Each rotation has determinant-one unitary representatives, with no claimed split lift. -/
theorem rotationMobius_unitary (g : rotationGroupThree) :
    ∃ A : Auxiliary.Algebra.SpecialLinear2, mobiusSpecialLinearProjection A = rotationMobiusHom g ∧
      Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2) := by
  apply (mobius_fixJ_iff_unitary_representative _).mp
  apply (mobiusBallConjugate_orthogonal_iff_fixJ _).mp
  exact ⟨g.val, rotationMobius_ball g⟩

/-- A rotation subgroup is represented by an actual Mobius subgroup with the same group law. -/
def rotationMobiusSubgroup (G : Subgroup rotationGroupThree) : Subgroup complexMobiusGroup :=
  G.map rotationMobiusHom

/-- This is a true group isomorphism onto the Mobius subgroup. -/
def rotationSubgroupEquiv (G : Subgroup rotationGroupThree) : G ≃* rotationMobiusSubgroup G :=
  G.equivMapOfInjective rotationMobiusHom rotationMobiusHom_injective

instance rotationMobiusSubgroup_finite (G : Subgroup rotationGroupThree) [Finite G] :
    Finite (rotationMobiusSubgroup G) :=
  Finite.of_surjective (rotationSubgroupEquiv G) (rotationSubgroupEquiv G).surjective

/-- Every finite rotation subgroup, including the regular-solid rotation groups, gives a finite Mobius group. -/
theorem finite_rotation_group_realization (G : Subgroup rotationGroupThree) [Finite G] :
    ∃ H : Subgroup complexMobiusGroup, Finite H ∧ Nonempty (G ≃* H) ∧
      ∀ f ∈ H, ∃ A : Auxiliary.Algebra.SpecialLinear2,
        mobiusSpecialLinearProjection A = f ∧ Auxiliary.Algebra.UnitaryMatrix (A :
          Auxiliary.Algebra.ComplexMatrix2) := by
  refine ⟨rotationMobiusSubgroup G, inferInstance, ⟨rotationSubgroupEquiv G⟩, ?_⟩
  intro f hf
  obtain ⟨g, _, rfl⟩ := hf
  exact rotationMobius_unitary g


/-- The binary lift is the full inverse image in SL2, rather than a nonexistent canonical split lift. -/
def rotationBinarySubgroup (G : Subgroup rotationGroupThree) : Subgroup Auxiliary.Algebra.SpecialLinear2 :=
  (rotationMobiusSubgroup G).comap mobiusSpecialLinearProjection

theorem rotationBinarySubgroup_unitary (G : Subgroup rotationGroupThree)
    (A : Auxiliary.Algebra.SpecialLinear2) (hA : A ∈ rotationBinarySubgroup G) :
    Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2) := by
  obtain ⟨g, _, hg⟩ := hA
  apply (mobiusSpecialLinearProjection_fixJ_iff A).mp
  rw [← hg]
  exact (mobius_fixJ_iff_unitary_representative _).mpr (rotationMobius_unitary g)

/-- The double-cover fibers make the full binary lift of a finite rotation group finite. -/
instance rotationBinarySubgroup_finite (G : Subgroup rotationGroupThree) [Finite G] :
    Finite (rotationBinarySubgroup G) := by
  have hf : ∀ f : complexMobiusGroup,
      Set.Finite (mobiusSpecialLinearProjection ⁻¹' {f}) := by
    intro f
    obtain ⟨A, B, _, _, _, hC⟩ := mobiusSpecialLinear_exactly_two_representatives f
    apply ((Set.finite_singleton B).insert A).subset
    intro C hCmem
    exact (Set.mem_insert_iff.mpr ((hC C).mp hCmem))
  have hH : Set.Finite (rotationMobiusSubgroup G : Set complexMobiusGroup) := by
    change Set.Finite (rotationMobiusHom '' (G : Set rotationGroupThree))
    exact (Set.toFinite (G : Set rotationGroupThree)).image rotationMobiusHom
  have hU : Set.Finite (⋃ f ∈ (rotationMobiusSubgroup G : Set complexMobiusGroup),
      mobiusSpecialLinearProjection ⁻¹' {f}) :=
    hH.biUnion (fun f _ => hf f)
  have hB : Set.Finite (rotationBinarySubgroup G : Set Auxiliary.Algebra.SpecialLinear2) := by
    apply hU.subset
    intro A hA
    exact Set.mem_iUnion.mpr ⟨mobiusSpecialLinearProjection A,
      Set.mem_iUnion.mpr ⟨hA, rfl⟩⟩
  exact hB.to_subtype

/-- The binary group maps onto the actual Mobius realization. -/
def rotationBinaryProjection (G : Subgroup rotationGroupThree) :
    rotationBinarySubgroup G →* rotationMobiusSubgroup G where
  toFun A := ⟨mobiusSpecialLinearProjection A.val, A.property⟩
  map_one' := by apply Subtype.ext; exact mobiusSpecialLinearProjection.map_one
  map_mul' A B := by apply Subtype.ext; exact mobiusSpecialLinearProjection.map_mul A.val B.val

theorem rotationBinaryProjection_surjective (G : Subgroup rotationGroupThree) :
    Function.Surjective (rotationBinaryProjection G) := by
  intro f
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective f.val
  refine ⟨⟨A, ?_⟩, ?_⟩
  · change mobiusSpecialLinearProjection A ∈ rotationMobiusSubgroup G
    rw [hA]
    exact f.property
  · apply Subtype.ext
    exact hA

/-- finite rotation groups have finite Mobius realizations and finite unitary binary covers. -/
theorem finite_rotation_group_unitary_cover (G : Subgroup rotationGroupThree) [Finite G] :
    ∃ B : Subgroup Auxiliary.Algebra.SpecialLinear2, Finite B ∧
      (∀ A ∈ B, Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2)) ∧
      B.map mobiusSpecialLinearProjection = rotationMobiusSubgroup G := by
  refine ⟨rotationBinarySubgroup G, inferInstance, rotationBinarySubgroup_unitary G, ?_⟩
  ext f
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact hA
  · intro hf
    obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
    exact ⟨A, hf, rfl⟩

end LowDimensionalTopology.Geometry.Mobius
