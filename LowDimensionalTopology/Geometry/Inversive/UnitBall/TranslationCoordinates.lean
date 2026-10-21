/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.Subgroup
public import LowDimensionalTopology.Geometry.Inversive.Distortion.MobiusDistortion
public import LowDimensionalTopology.Geometry.Inversive.Topology.Uniform
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.Matrix.Normed
public import LowDimensionalTopology.Geometry.Euclidean.OrthogonalNormalForm
/-!
# Pure translations and the ball boundary topology

The pure translation is exactly the specified plane/sphere reflection
composition, with the identity at zero. It preserves the actual diameter
and sends its parameter to zero. Every ball preserver has a unique
orthogonal-map/pure-translation decomposition.

The ball-group metric is induced by the actual boundary action; its explicit
formula is uniform Euclidean distance on the unit sphere, and Cayley
conjugacy is an isometry. Evaluation at zero is continuous and surjective;
the pure-translation parameterization is a homeomorphism onto its actual
range. Operator-norm and matrix Frobenius topologies agree on the orthogonal
group. The full orthogonal-map/pure-translation decomposition is a
homeomorphism, including its realization by standard orthogonal matrices.
-/
@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Set Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

def pureTranslationCenter (a : Hyperbolic.unitBallDomain n) : Euclidean n := unitInversion a.val

def pureTranslationRadius (a : Hyperbolic.unitBallDomain n) : ℝ := Real.sqrt (‖pureTranslationCenter a‖^2-1)

theorem pureTranslationCenter_norm_gt_one (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    1 < ‖pureTranslationCenter a‖ := by
  rw [pureTranslationCenter,norm_unitInversion]
  exact (one_lt_inv₀ (norm_pos_iff.mpr ha)).mpr (Hyperbolic.unitBallDomain_norm_lt a)

theorem pureTranslationRadius_pos (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) : 0 < pureTranslationRadius a := by
  apply Real.sqrt_pos.mpr
  have hc := pureTranslationCenter_norm_gt_one a ha
  nlinarith

theorem pureTranslationSphere_orthogonal (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    ‖pureTranslationCenter a‖^2 = 1+pureTranslationRadius a^2 := by
  have hc := pureTranslationCenter_norm_gt_one a ha
  rw [pureTranslationRadius,Real.sq_sqrt (by nlinarith : 0 ≤ ‖pureTranslationCenter a‖^2-1)]
  ring

def pureTranslationSphere (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) : ExtendedHomeomorph n :=
  sphereInversionHomeomorph (pureTranslationCenter a) (pureTranslationRadius a)
    (pureTranslationRadius_pos a ha).ne'

theorem pureTranslationSphere_preservesUnitBall (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    PreservesUnitBall (pureTranslationSphere a ha) :=
  sphereInversion_preservesUnitBall_of_boundaryOrthogonal (pureTranslationCenter a) (pureTranslationRadius a)
    (pureTranslationRadius_pos a ha) (pureTranslationSphere_orthogonal a ha)

theorem pureTranslationSphere_isReflection (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    IsReflection (pureTranslationSphere a ha) :=
  sphereInversion_isReflection (pureTranslationCenter a) (pureTranslationRadius a) (pureTranslationRadius_pos a ha)

theorem pureTranslationSphere_zero (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    pureTranslationSphere a ha (0 : Euclidean n) = a.val := by
  have hc := pureTranslationCenter_norm_gt_one a ha
  have hc0 : pureTranslationCenter a ≠ 0 := by intro h; rw [h,norm_zero] at hc; linarith
  change sphereInversion (pureTranslationCenter a) (pureTranslationRadius a) (0 : Euclidean n) = _
  rw [sphereInversion_coe _ _ (Ne.symm hc0),boundaryOrthogonal_inversion_zero _ _ hc0
    (pureTranslationSphere_orthogonal a ha)]
  apply congrArg OnePoint.some
  exact (by
    simpa only [pureTranslationCenter,inversion_unit] using
      inversion_inversion (0 : Euclidean n) one_ne_zero a.val)

theorem pureTranslationSphere_apply_self (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    pureTranslationSphere a ha a.val = (0 : Euclidean n) := by
  rw [← pureTranslationSphere_zero a ha]
  exact sphereInversion_involutive (pureTranslationCenter a) (pureTranslationRadius_pos a ha).ne' (0 : Euclidean n)

def pureTranslation (a : Hyperbolic.unitBallDomain n) : ExtendedHomeomorph n :=
  if ha : a.val = 0 then 1 else planeReflectionHomeomorph a.val 0 ha * pureTranslationSphere a ha

theorem pureTranslation_origin (n : ℕ) : pureTranslation (Hyperbolic.ballOrigin n) = 1 := by
  simp [pureTranslation,Hyperbolic.ballOrigin]

theorem pureTranslation_eq_reflections (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    pureTranslation a = planeReflectionHomeomorph a.val 0 ha * pureTranslationSphere a ha := by
  simp [pureTranslation,ha]

theorem pureTranslation_preservesUnitBall (a : Hyperbolic.unitBallDomain n) : PreservesUnitBall (pureTranslation
    a) := by
  by_cases ha : a.val = 0
  · simp only [pureTranslation,dite_eq_left ha]
    change (id : ExtendedEuclidean n → ExtendedEuclidean n) '' extendedUnitBall = extendedUnitBall
    exact Set.image_id _
  · rw [pureTranslation_eq_reflections a ha]
    exact (planeReflection_preservesUnitBall_zero a.val ha).mul (pureTranslationSphere_preservesUnitBall a ha)

theorem pureTranslation_mem_generalMobiusGroup (a : Hyperbolic.unitBallDomain n) : pureTranslation a ∈
    generalMobiusGroup n := by
  by_cases ha : a.val = 0
  · simp only [pureTranslation,dite_eq_left ha]
    exact (generalMobiusGroup n).one_mem
  · rw [pureTranslation_eq_reflections a ha]
    exact (generalMobiusGroup n).mul_mem (planeReflection_isReflection a.val 0 ha).mem_generalMobiusGroup
      (pureTranslationSphere_isReflection a ha).mem_generalMobiusGroup

theorem pureTranslation_apply_self (a : Hyperbolic.unitBallDomain n) : pureTranslation a a.val = (0 : Euclidean n) := by
  by_cases ha : a.val = 0
  · simp [pureTranslation,ha]
  · rw [pureTranslation_eq_reflections a ha]
    change planeReflectionHomeomorph a.val 0 ha (pureTranslationSphere a ha a.val) = _
    rw [pureTranslationSphere_apply_self]
    apply congrArg OnePoint.some
    exact (planeReflectionFinite_fixed_iff a.val 0 ha 0).mpr (inner_zero_left _)

theorem pureTranslation_inv_zero (a : Hyperbolic.unitBallDomain n) :
    (pureTranslation a)⁻¹ (0 : Euclidean n) = (a.val : ExtendedEuclidean n) := by
  apply (pureTranslation a).injective
  exact ((pureTranslation a).apply_symm_apply (0 : Euclidean n)).trans (pureTranslation_apply_self a).symm

def pureTranslationBall (a : Hyperbolic.unitBallDomain (n+1)) : ballPreservingSubgroup n :=
  ⟨⟨pureTranslation a,pureTranslation_mem_generalMobiusGroup a⟩,pureTranslation_preservesUnitBall a⟩

def ballDiameter (a : Euclidean n) : Set (ExtendedEuclidean n) :=
  ((↑) : Euclidean n → ExtendedEuclidean n) '' {x | ‖x‖ < 1 ∧ x ∈ ℝ ∙ a}

theorem involutive_image_eq_of_mapsTo {X : Type*} (f : X → X) (hf : Function.Involutive f)
    (S : Set X) (hS : MapsTo f S S) : f '' S = S := by
  apply Subset.antisymm hS.image_subset
  intro x hx
  exact ⟨f x,hS hx,hf x⟩

theorem IsReflection.involutive {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    Function.Involutive f := by
  intro x
  have h := f.apply_symm_apply x
  change f ((f⁻¹ : ExtendedHomeomorph n) x) = x at h
  rwa [hf.inv_eq] at h

theorem planeReflection_image_ballDiameter (a : Euclidean n) (ha : a ≠ 0) :
    planeReflectionHomeomorph a 0 ha '' ballDiameter a = ballDiameter a := by
  apply involutive_image_eq_of_mapsTo _ (planeReflection_isReflection a 0 ha).involutive
  rintro z ⟨x,⟨hx,hspan⟩,rfl⟩
  refine ⟨planeReflectionFinite a 0 x,⟨?_,?_⟩,rfl⟩
  · rw [← cartanPlaneLinearIsometry_apply,(cartanPlaneLinearIsometry a).norm_map]
    exact hx
  · unfold planeReflectionFinite
    exact (ℝ ∙ a).sub_mem hspan ((ℝ ∙ a).smul_mem _ (Submodule.mem_span_singleton_self a))

theorem pureTranslationSphere_image_ballDiameter (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    pureTranslationSphere a ha '' ballDiameter a.val = ballDiameter a.val := by
  apply involutive_image_eq_of_mapsTo _ (pureTranslationSphere_isReflection a ha).involutive
  rintro z ⟨x,⟨hx,hspan⟩,rfl⟩
  obtain ⟨hxc,hi⟩ := boundaryOrthogonal_inversion_maps_ball (pureTranslationCenter a) x (pureTranslationRadius a)
    (pureTranslationRadius_pos a ha) (pureTranslationSphere_orthogonal a ha) hx
  refine ⟨inversion (pureTranslationCenter a) (pureTranslationRadius a) x,⟨hi,?_⟩,?_⟩
  · have hc : pureTranslationCenter a ∈ ℝ ∙ a.val :=
      (ℝ ∙ a.val).smul_mem _ (Submodule.mem_span_singleton_self a.val)
    rw [inversion_formula]
    exact (ℝ ∙ a.val).add_mem hc ((ℝ ∙ a.val).smul_mem _ ((ℝ ∙ a.val).sub_mem hspan hc))
  · exact (sphereInversion_coe _ _ hxc).symm

theorem pureTranslation_image_ballDiameter (a : Hyperbolic.unitBallDomain n) :
    pureTranslation a '' ballDiameter a.val = ballDiameter a.val := by
  by_cases ha : a.val = 0
  · simp only [pureTranslation,dite_eq_left ha]
    exact Set.image_id _
  · rw [pureTranslation_eq_reflections a ha]
    change (planeReflectionHomeomorph a.val 0 ha ∘ pureTranslationSphere a ha) '' ballDiameter a.val = _
    rw [Set.image_comp,pureTranslationSphere_image_ballDiameter a ha,planeReflection_image_ballDiameter a.val ha]

theorem PreservesUnitBall.inverse {f : ExtendedHomeomorph n} (hf : PreservesUnitBall f) :
    PreservesUnitBall (f⁻¹ : ExtendedHomeomorph n) := by
  have h := homeomorph_inv_image_image f extendedUnitBall
  rw [hf] at h
  exact h

theorem cartanLinearExtensionHom_injective : Function.Injective (cartanLinearExtensionHom (n := n)) := by
  intro L K h
  ext x : 1
  apply OnePoint.coe_injective
  exact congrArg (fun f : ExtendedHomeomorph n => f x) h

theorem pureTranslation_decomposition_exists [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f) :
    ∃ L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n, ∃ a : Hyperbolic.unitBallDomain n,
      f = cartanLinearExtensionHom L * pureTranslation a := by
  let a : Hyperbolic.unitBallDomain n := Hyperbolic.ballHomeomorph f⁻¹ hB.inverse (Hyperbolic.ballOrigin n)
  have ha0 : f a.val = (0 : Euclidean n) := by
    have ha := Hyperbolic.ballHomeomorph_coe f⁻¹ hB.inverse (Hyperbolic.ballOrigin n)
    change (a.val : ExtendedEuclidean n) = f.symm (0 : Euclidean n) at ha
    rw [ha,f.apply_symm_apply]
  let g := f * (pureTranslation a)⁻¹
  have hg : g ∈ generalMobiusGroup n := (generalMobiusGroup n).mul_mem hf
    ((generalMobiusGroup n).inv_mem (pureTranslation_mem_generalMobiusGroup a))
  have hgB : PreservesUnitBall g := hB.mul (pureTranslation_preservesUnitBall a).inverse
  have hg0 : g (0 : Euclidean n) = (0 : Euclidean n) := by
    change f ((pureTranslation a)⁻¹ (0 : Euclidean n)) = _
    rw [pureTranslation_inv_zero,ha0]
  obtain ⟨L,hL⟩ := ball_preserving_fix_zero_linearIsometry g hg hgB hg0
  refine ⟨L,a,?_⟩
  rw [← hL]
  dsimp only [g]
  group

theorem pureTranslation_decomposition_unique
    {L K : Euclidean n ≃ₗᵢ[ℝ] Euclidean n} {a b : Hyperbolic.unitBallDomain n}
    (h : cartanLinearExtensionHom L * pureTranslation a = cartanLinearExtensionHom K * pureTranslation b) :
    L = K ∧ a = b := by
  have he0 : (cartanLinearExtensionHom K * pureTranslation b) a.val = (0 : Euclidean n) := by
    rw [← h]
    change cartanLinearExtensionHom L (pureTranslation a a.val) = _
    rw [pureTranslation_apply_self,cartanLinearExtensionHom_coe,L.map_zero]
  have he0' : (cartanLinearExtensionHom K * pureTranslation b) b.val = (0 : Euclidean n) := by
    change cartanLinearExtensionHom K (pureTranslation b b.val) = _
    rw [pureTranslation_apply_self,cartanLinearExtensionHom_coe,K.map_zero]
  have hab : a = b := Subtype.ext (OnePoint.coe_injective
    ((cartanLinearExtensionHom K * pureTranslation b).injective (he0.trans he0'.symm)))
  subst b
  exact ⟨cartanLinearExtensionHom_injective (mul_right_cancel h),rfl⟩

def orthogonalPureTranslationMap (p : (Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) × Hyperbolic.unitBallDomain (n+1)) :
    ballPreservingSubgroup n :=
  ⟨⟨cartanLinearExtensionHom p.1 * pureTranslation p.2,
    (generalMobiusGroup (n+1)).mul_mem (extendedIsometry_mem_generalMobiusGroup p.1.toIsometryEquiv)
      (pureTranslation_mem_generalMobiusGroup p.2)⟩,
    (cartanLinearExtension_preservesUnitBall p.1).mul (pureTranslation_preservesUnitBall p.2)⟩

theorem orthogonalPureTranslationMap_bijective : Function.Bijective (orthogonalPureTranslationMap (n := n)) := by
  constructor
  · rintro ⟨L,a⟩ ⟨K,b⟩ h
    have hh := congrArg (fun f : ballPreservingSubgroup n => f.val.val) h
    obtain ⟨hL,ha⟩ := pureTranslation_decomposition_unique hh
    exact Prod.ext hL ha
  · intro f
    obtain ⟨L,a,ha⟩ := pureTranslation_decomposition_exists f.val.val f.val.property f.property
    refine ⟨⟨L,a⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ha.symm

def orthogonalPureTranslationEquiv (n : ℕ) :
    ((Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) × Hyperbolic.unitBallDomain (n+1)) ≃ ballPreservingSubgroup n :=
  Equiv.ofBijective orthogonalPureTranslationMap orthogonalPureTranslationMap_bijective

def pureTranslationBallHomeomorph (a : Hyperbolic.unitBallDomain n) : Hyperbolic.unitBallDomain n ≃ₜ
    Hyperbolic.unitBallDomain n :=
  Hyperbolic.ballHomeomorph (pureTranslation a) (pureTranslation_preservesUnitBall a)

theorem pureTranslation_pathDist [NeZero n] (a x y : Hyperbolic.unitBallDomain n) :
    (Hyperbolic.ballDensity n).pathDist (pureTranslationBallHomeomorph a x) (pureTranslationBallHomeomorph a y) =
      (Hyperbolic.ballDensity n).pathDist x y :=
  Hyperbolic.ballDensity_pathDist_invariant (pureTranslation a) (pureTranslation_mem_generalMobiusGroup a)
    (pureTranslation_preservesUnitBall a) x y

theorem pureTranslation_decomposition_parameter (f : ExtendedHomeomorph n)
    (L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) (a : Hyperbolic.unitBallDomain n)
    (he : f = cartanLinearExtensionHom L * pureTranslation a) :
    (f⁻¹ : ExtendedHomeomorph n) (0 : Euclidean n) = (a.val : ExtendedEuclidean n) := by
  apply f.injective
  change f (f.symm (0 : Euclidean n)) = f a.val
  rw [f.apply_symm_apply,he]
  change ((0 : Euclidean n) : ExtendedEuclidean n) = cartanLinearExtensionHom L (pureTranslation a a.val)
  rw [pureTranslation_apply_self,cartanLinearExtensionHom_coe,L.map_zero]

theorem pureTranslationRadius_sq (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0) :
    pureTranslationRadius a^2 = (1-‖a.val‖^2)/‖a.val‖^2 := by
  have hh := pureTranslationSphere_orthogonal a ha
  rw [pureTranslationCenter,norm_sq_unitInversion a.val ha] at hh
  field_simp [norm_ne_zero_iff.mpr ha] at hh ⊢
  nlinarith

theorem unitSphere_inverseCenter_distance_sq (a x : Euclidean n) (ha : a ≠ 0) (hx : ‖x‖ = 1) :
    ‖x-unitInversion a‖^2 = ‖x-a‖^2/‖a‖^2 := by
  rw [norm_sub_sq_real,norm_sub_sq_real,norm_sq_unitInversion a ha,hx,unitInversion,real_inner_smul_right]
  field_simp [norm_ne_zero_iff.mpr ha]
  ring

theorem pureTranslation_boundary_scale (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    (pureTranslationRadius a/‖x-pureTranslationCenter a‖)^2 = (1-‖a.val‖^2)/‖x-a.val‖^2 := by
  have hxa : x ≠ a.val := by intro he; rw [he] at hx; have h := Hyperbolic.unitBallDomain_norm_lt a; linarith
  rw [div_pow,pureTranslationRadius_sq a ha,pureTranslationCenter,unitSphere_inverseCenter_distance_sq a.val x ha hx]
  field_simp [norm_ne_zero_iff.mpr ha,norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)]

theorem pureTranslation_boundary_formula_nonzero (a : Hyperbolic.unitBallDomain n) (ha : a.val ≠ 0)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    finiteEuclideanPart (pureTranslation a) x =
      -a.val + ((1-‖a.val‖^2)/‖x-a.val‖^2) • (x-a.val) := by
  have hxc : x ≠ pureTranslationCenter a := by
    intro he
    rw [he] at hx
    have hc := pureTranslationCenter_norm_gt_one a ha
    linarith
  have hfin : finiteEuclideanPart (pureTranslation a) x =
      cartanPlaneLinearIsometry a.val (inversion (pureTranslationCenter a) (pureTranslationRadius a) x) := by
    rw [pureTranslation_eq_reflections a ha,← cartanLinearExtension_plane a.val ha,finiteEuclideanPart_linear_mul]
    change cartanPlaneLinearIsometry a.val ((sphereInversion (pureTranslationCenter a) (pureTranslationRadius a)
      x).elim 0 id) = _
    rw [sphereInversion_coe _ _ hxc]
    rfl
  let L := cartanPlaneLinearIsometry a.val
  have hLa : L a.val = -a.val := Submodule.reflection_orthogonalComplement_singleton_eq_neg a.val
  have hLc : L (pureTranslationCenter a) = -pureTranslationCenter a := by
    change L ((‖a.val‖^2)⁻¹ • a.val) = -((‖a.val‖^2)⁻¹ • a.val)
    rw [L.map_smul,hLa,smul_neg]
  have hLx : L x = x-(2*(inner ℝ x a.val)/‖a.val‖^2) • a.val := by
    rw [cartanPlaneLinearIsometry_apply,planeReflectionFinite,sub_zero]
  rw [hfin]
  change L (inversion (pureTranslationCenter a) (pureTranslationRadius a) x) = _
  rw [inversion_formula,L.map_add,L.map_smul,L.map_sub,hLc,hLx,pureTranslation_boundary_scale a ha x
    hx,pureTranslationCenter,unitInversion]
  have hd : ‖x-a.val‖^2 = 1-2*inner ℝ x a.val+‖a.val‖^2 := by
    rw [norm_sub_sq_real,hx]
    ring
  have hxa : x ≠ a.val := by intro he; rw [he] at hx; have h := Hyperbolic.unitBallDomain_norm_lt a; linarith
  have hs : ‖a.val‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  have hdx : ‖x-a.val‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa))
  have hk : ((1-‖a.val‖^2)/‖x-a.val‖^2) * (1-2*inner ℝ x a.val+‖a.val‖^2) = 1-‖a.val‖^2 := by
    rw [← hd]
    exact div_mul_cancel₀ _ hdx
  match_scalars
  field_simp [hs,hdx]
  linear_combination hk
  rfl

theorem pureTranslation_boundary_formula (a : Hyperbolic.unitBallDomain n) (x : Euclidean n) (hx : ‖x‖ = 1) :
    finiteEuclideanPart (pureTranslation a) x =
      -a.val + ((1-‖a.val‖^2)/‖x-a.val‖^2) • (x-a.val) := by
  by_cases ha : a.val = 0
  · simp [pureTranslation,ha,hx,finiteEuclideanPart]
  · exact pureTranslation_boundary_formula_nonzero a ha x hx

theorem boundaryOrthogonal_inversion_antipodal_sum (c u : Euclidean n) (r : ℝ)
    (horth : ‖c‖^2 = 1+r^2) (hu : ‖u‖ = 1) (huc : inner ℝ u c = 0) :
    inversion c r u + inversion c r (-u) = (4/(1+‖c‖^2)) • c := by
  have hd : ‖u-c‖^2 = 1+‖c‖^2 := by rw [norm_sub_sq_real,hu,huc]; ring
  have hd' : ‖-u-c‖^2 = 1+‖c‖^2 := by rw [norm_sub_sq_real,norm_neg,hu,inner_neg_left,huc]; ring
  rw [inversion_formula,inversion_formula,div_pow,div_pow,hd,hd']
  match_scalars <;> field_simp <;> nlinarith only [horth]

theorem ballOrigin_norm_le_of_boundary_bound [NeZero n] (f : ExtendedHomeomorph (n+1))
    (hf : f ∈ generalMobiusGroup (n+1)) (hB : PreservesUnitBall f) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ x : Euclidean (n+1), ‖x‖ = 1 → dist (finiteEuclideanPart f x) x ≤ ε) :
    ‖(Hyperbolic.ballHomeomorph f hB (Hyperbolic.ballOrigin (n+1))).val‖ ≤ ε := by
  by_cases hi : f ∞ = ∞
  · have h0 := generalMobius_ball_fixing_infty_fixes_zero f hf hB hi
    rw [Hyperbolic.ballHomeomorph_val]
    change ‖(f (0 : Euclidean (n+1))).elim 0 id‖ ≤ ε
    rw [h0]
    change ‖(0 : Euclidean (n+1))‖ ≤ ε
    simpa only [norm_zero] using hε
  · obtain ⟨c,r,hr,horth,L,rfl⟩ := generalMobius_ball_nonAffine_orthogonal_reflection f hf hB hi
    have hc : 1 < ‖c‖ := by nlinarith [norm_nonneg c,sq_pos_of_pos hr]
    have hc0 : c ≠ 0 := by intro he; rw [he,norm_zero] at hc; linarith
    obtain ⟨u,hu,hcu⟩ := exists_orthogonal_unit_vector (by have h := NeZero.pos n; omega : 2 ≤ n+1) c hc0
    have huc : inner ℝ u c = 0 := by rw [real_inner_comm]; exact hcu
    let F := cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne'
    have hval (z : Euclidean (n+1)) (hz : ‖z‖ = 1) : finiteEuclideanPart F z = L (inversion c r z) := by
      have hzc : z ≠ c := by intro he; rw [he] at hz; linarith
      rw [finiteEuclideanPart_linear_mul]
      change L ((sphereInversion c r z).elim 0 id) = _
      rw [sphereInversion_coe c r hzc]
      rfl
    have huneg : ‖-u‖ = 1 := by rw [norm_neg,hu]
    have hsum : ‖finiteEuclideanPart F u+finiteEuclideanPart F (-u)‖ = 4*‖c‖/(1+‖c‖^2) := by
      rw [hval u hu,hval (-u) huneg,← L.map_add,boundaryOrthogonal_inversion_antipodal_sum c u r horth hu huc,
        L.map_smul,norm_smul,L.norm_map,Real.norm_eq_abs,abs_of_pos (by positivity : (0:ℝ) < 4/(1+‖c‖^2))]
      ring
    have hsumBound : 4*‖c‖/(1+‖c‖^2) ≤ 2*ε := by
      rw [← hsum]
      calc
        _ = ‖(finiteEuclideanPart F u-u)+(finiteEuclideanPart F (-u)-(-u))‖ := by congr 1; module
        _ ≤ ‖finiteEuclideanPart F u-u‖+‖finiteEuclideanPart F (-u)-(-u)‖ := norm_add_le _ _
        _ = dist (finiteEuclideanPart F u) u+dist (finiteEuclideanPart F (-u)) (-u) := by simp only [dist_eq_norm]
        _ ≤ ε+ε := add_le_add (hbound u hu) (hbound (-u) huneg)
        _ = _ := by ring
    have ha : 0 < ‖c‖ := zero_lt_one.trans hc
    have hlo : 2/‖c‖ ≤ 4*‖c‖/(1+‖c‖^2) := by
      apply (div_le_div_iff₀ ha (by positivity)).mpr
      nlinarith
    rw [ballHomeomorph_sphere_origin_norm L c r hr hc horth]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha).mpr
    have hh := (div_le_iff₀ ha).mp (hlo.trans hsumBound)
    nlinarith

section BoundaryMetric
variable [NeZero n]
local instance pureTranslationBoundaryChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n
local instance pureTranslationBoundaryMobiusMetric : MetricSpace (GM n) := mobiusUniformMetricSpace n

abbrev ballMobiusUniformMetricSpace (n : ℕ) [NeZero n] : MetricSpace (ballPreservingSubgroup n) :=
  MetricSpace.induced (Hyperbolic.cayleyPoincareEquiv (n := n)).symm (Hyperbolic.cayleyPoincareEquiv (n :=
    n)).symm.injective
    (mobiusUniformMetricSpace n)

local instance pureTranslationBallMobiusMetric : MetricSpace (ballPreservingSubgroup n) :=
    ballMobiusUniformMetricSpace n
-- Fix the boundary metric projections on this nested subgroup explicitly.
local instance (priority := 2000) pureTranslationBallPseudoMetric : PseudoMetricSpace (ballPreservingSubgroup n) :=
  (ballMobiusUniformMetricSpace n).toPseudoMetricSpace
local instance (priority := 2000) pureTranslationBallPseudoEMetric : PseudoEMetricSpace (ballPreservingSubgroup n) :=
  (ballMobiusUniformMetricSpace n).toEMetricSpace.toPseudoEMetricSpace
local instance (priority := 2000) pureTranslationBallDist : Dist (ballPreservingSubgroup n) :=
  (ballMobiusUniformMetricSpace n).toDist
local instance (priority := 2000) pureTranslationBallEDist : EDist (ballPreservingSubgroup n) :=
  (ballMobiusUniformMetricSpace n).toEDist
local instance (priority := 2000) pureTranslationBallUniform : UniformSpace (ballPreservingSubgroup n) :=
  (ballMobiusUniformMetricSpace n).toUniformSpace
local instance (priority := 2000) pureTranslationBallTopology : TopologicalSpace (ballPreservingSubgroup n) :=
  (ballMobiusUniformMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace


theorem cayleyPoincareEquiv_symm_isometry : Isometry (Hyperbolic.cayleyPoincareEquiv (n := n)).symm :=
  MetricSpace.isometry_induced _ (Hyperbolic.cayleyPoincareEquiv (n := n)).symm.injective

theorem cayleyPoincareEquiv_isometry : Isometry (Hyperbolic.cayleyPoincareEquiv (n := n)) := by
  intro f g
  simpa only [MulEquiv.symm_apply_apply] using (cayleyPoincareEquiv_symm_isometry (n := n)
    ((Hyperbolic.cayleyPoincareEquiv (n := n)) f)
    ((Hyperbolic.cayleyPoincareEquiv (n := n)) g)).symm

theorem cayleyPoincareEquiv_symm_boundary (f : ballPreservingSubgroup n) :
    ((Hyperbolic.cayleyPoincareEquiv (n := n)).symm f : ExtendedHomeomorph n) =
      Hyperbolic.ballBoundaryAction f.val.val f.property := by
  have he : f.val.val = Hyperbolic.cayleyBall n *
      (Hyperbolic.poincareExtension ((Hyperbolic.cayleyPoincareEquiv (n := n)).symm f) : ExtendedHomeomorph (n+1))
        * (Hyperbolic.cayleyBall n)⁻¹ := by
    have hh := congrArg (fun k : ballPreservingSubgroup n => k.val.val)
      ((Hyperbolic.cayleyPoincareEquiv (n := n)).apply_symm_apply f)
    exact hh.symm
  have hh := ballBoundaryAction_cayley_poincare ((Hyperbolic.cayleyPoincareEquiv (n := n)).symm f)
  have hcongr : Hyperbolic.ballBoundaryAction f.val.val f.property =
      Hyperbolic.ballBoundaryAction (Hyperbolic.cayleyBall n * (Hyperbolic.poincareExtension
        ((Hyperbolic.cayleyPoincareEquiv (n := n)).symm f) : ExtendedHomeomorph (n+1)) * (Hyperbolic.cayleyBall n)⁻¹)
        (Hyperbolic.cayleyBall_poincare_conjugate_preservesUnitBall ((Hyperbolic.cayleyPoincareEquiv (n :=
          n)).symm f)) := by
    congr 1
  exact (hcongr.trans hh).symm

theorem ballMobius_uniform_dist_eq_boundary (f g : ballPreservingSubgroup n) :
    dist f g = ⨆ x : Metric.sphere (0 : Euclidean (n+1)) 1,
      dist (finiteEuclideanPart f.val.val x.val) (finiteEuclideanPart g.val.val x.val) := by
  change dist ((Hyperbolic.cayleyPoincareEquiv (n := n)).symm f) ((Hyperbolic.cayleyPoincareEquiv (n := n)).symm g) = _
  rw [mobius_uniform_dist_eq_iSup]
  simp only [cayleyPoincareEquiv_symm_boundary]
  calc
    _ = ⨆ x : ExtendedEuclidean n,
        dist (finiteEuclideanPart f.val.val (stereographicHomeomorph n x).val)
          (finiteEuclideanPart g.val.val (stereographicHomeomorph n x).val) := by
      apply iSup_congr
      intro x
      change dist (stereographicHomeomorph n (Hyperbolic.ballBoundaryAction f.val.val f.property x)).val
        (stereographicHomeomorph n (Hyperbolic.ballBoundaryAction g.val.val g.property x)).val = _
      exact congrArg₂ (fun u v : Euclidean (n+1) => dist u v)
        (ballBoundaryAction_stereographic f.val.val (show PreservesUnitBall f.val.val from f.property) x)
        (ballBoundaryAction_stereographic g.val.val (show PreservesUnitBall g.val.val from g.property) x)
    _ = _ := (stereographicHomeomorph n).toEquiv.iSup_comp
      (g := fun x : Metric.sphere (0 : Euclidean (n+1)) 1 =>
        dist (finiteEuclideanPart f.val.val x.val) (finiteEuclideanPart g.val.val x.val))

instance ballMobius_isTopologicalGroup : IsTopologicalGroup (ballPreservingSubgroup n) :=
  isTopologicalGroup_induced (Hyperbolic.cayleyPoincareEquiv (n := n)).symm

def ballBoundaryContinuousMap (f : ballPreservingSubgroup n) :
    C(Metric.sphere (0 : Euclidean (n+1)) 1,Euclidean (n+1)) where
  toFun x := (stereographicHomeomorph n (Hyperbolic.ballBoundaryAction f.val.val f.property
    ((stereographicHomeomorph n).symm x))).val
  continuous_toFun := continuous_subtype_val.comp ((stereographicHomeomorph n).continuous.comp
    ((Hyperbolic.ballBoundaryAction f.val.val f.property).continuous.comp (stereographicHomeomorph n).symm.continuous))

omit [NeZero n] in
theorem ballBoundaryContinuousMap_apply (f : ballPreservingSubgroup n)
    (x : Metric.sphere (0 : Euclidean (n+1)) 1) :
    ballBoundaryContinuousMap f x = finiteEuclideanPart f.val.val x.val := by
  change (stereographicHomeomorph n (Hyperbolic.ballBoundaryAction f.val.val f.property ((stereographicHomeomorph
    n).symm x))).val = _
  have h := ballBoundaryAction_stereographic f.val.val (show PreservesUnitBall f.val.val from f.property)
    ((stereographicHomeomorph n).symm x)
  rw [(stereographicHomeomorph n).apply_symm_apply] at h
  exact h

theorem ballBoundaryContinuousMap_isometry : Isometry (ballBoundaryContinuousMap (n := n)) := by
  apply Isometry.of_dist_eq
  intro f g
  rw [ContinuousMap.dist_eq_iSup,ballMobius_uniform_dist_eq_boundary]
  apply iSup_congr
  intro x
  rw [ballBoundaryContinuousMap_apply,ballBoundaryContinuousMap_apply]

omit [NeZero n] in
theorem pureTranslation_boundary_joint_continuous :
    Continuous (fun p : Hyperbolic.unitBallDomain (n+1) × Metric.sphere (0 : Euclidean (n+1)) 1 =>
      finiteEuclideanPart (pureTranslation p.1) p.2.val) := by
  have hformula : (fun p : Hyperbolic.unitBallDomain (n+1) × Metric.sphere (0 : Euclidean (n+1)) 1 =>
      finiteEuclideanPart (pureTranslation p.1) p.2.val) =
      (fun p => -p.1.val+((1-‖p.1.val‖^2)/‖p.2.val-p.1.val‖^2) • (p.2.val-p.1.val)) := by
    funext p
    exact pureTranslation_boundary_formula p.1 p.2.val (by
      simpa only [Metric.mem_sphere,dist_zero_right] using p.2.property)
  rw [hformula]
  apply continuous_fst.subtype_val.neg.add
    (((continuous_const.sub (continuous_fst.subtype_val.norm.pow 2)).div
      ((continuous_snd.subtype_val.sub continuous_fst.subtype_val).norm.pow 2) ?_).smul
      (continuous_snd.subtype_val.sub continuous_fst.subtype_val))
  rintro ⟨a,x⟩
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  apply sub_ne_zero.mpr
  intro he
  change x.val = a.val at he
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.property
  rw [he] at hx
  have ha := Hyperbolic.unitBallDomain_norm_lt a
  linarith

theorem pureTranslationBall_continuous : Continuous (pureTranslationBall (n := n)) := by
  apply ballBoundaryContinuousMap_isometry.comp_continuous_iff.mp
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (Function.uncurry fun a x => ballBoundaryContinuousMap (pureTranslationBall a) x)
  have he : (Function.uncurry fun a x => ballBoundaryContinuousMap (pureTranslationBall a) x) =
      (fun p : Hyperbolic.unitBallDomain (n+1) × Metric.sphere (0 : Euclidean (n+1)) 1 =>
        finiteEuclideanPart (pureTranslation p.1) p.2.val) := by
    funext p
    exact ballBoundaryContinuousMap_apply (pureTranslationBall p.1) p.2
  rw [he]
  exact pureTranslation_boundary_joint_continuous

theorem ballMobius_boundary_dist_le (f g : ballPreservingSubgroup n)
    (x : Metric.sphere (0 : Euclidean (n+1)) 1) :
    dist (finiteEuclideanPart f.val.val x.val) (finiteEuclideanPart g.val.val x.val) ≤ dist f g := by
  have h := ContinuousMap.dist_apply_le_dist (f := ballBoundaryContinuousMap f) (g := ballBoundaryContinuousMap g) x
  rw [ballBoundaryContinuousMap_apply,ballBoundaryContinuousMap_apply,ballBoundaryContinuousMap_isometry.dist_eq] at h
  exact h

def ballMobiusOrigin (f : ballPreservingSubgroup n) : Hyperbolic.unitBallDomain (n+1) :=
  Hyperbolic.ballHomeomorph f.val.val f.property (Hyperbolic.ballOrigin (n+1))

theorem ballMobiusOrigin_norm_le_dist_one (f : ballPreservingSubgroup n) :
    ‖(ballMobiusOrigin f).val‖ ≤ dist f 1 := by
  apply ballOrigin_norm_le_of_boundary_bound f.val.val f.val.property f.property _ dist_nonneg
  intro x hx
  exact ballMobius_boundary_dist_le f 1 ⟨x,by rw [Metric.mem_sphere,dist_zero_right,hx]⟩

omit [NeZero n] in
theorem ballMobiusOrigin_one : ballMobiusOrigin (1 : ballPreservingSubgroup n) = Hyperbolic.ballOrigin (n+1) := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  exact Hyperbolic.ballHomeomorph_coe (1 : ExtendedHomeomorph (n+1))
    (show PreservesUnitBall (1 : ExtendedHomeomorph (n+1)) from (1 : ballPreservingSubgroup n).property)
      (Hyperbolic.ballOrigin (n+1))

theorem ballMobiusOrigin_continuousAt_one : ContinuousAt (ballMobiusOrigin (n := n)) 1 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε,hε,?_⟩
  intro f hf
  rw [ballMobiusOrigin_one]
  change dist (ballMobiusOrigin f).val 0 < ε
  rw [dist_zero_right]
  exact (ballMobiusOrigin_norm_le_dist_one f).trans_lt hf

omit [NeZero n] in
theorem ballMobiusOrigin_left_translate (g f : ballPreservingSubgroup n) :
    ballMobiusOrigin f = Hyperbolic.ballHomeomorph g.val.val g.property (ballMobiusOrigin (g⁻¹*f)) := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  have h1 : ((ballMobiusOrigin f).val : ExtendedEuclidean (n+1)) = f.val.val (0 : Euclidean (n+1)) :=
    Hyperbolic.ballHomeomorph_coe f.val.val f.property (Hyperbolic.ballOrigin (n+1))
  have h2 : ((ballMobiusOrigin (g⁻¹*f)).val : ExtendedEuclidean (n+1)) =
      g.val.val.symm (f.val.val (0 : Euclidean (n+1))) :=
    Hyperbolic.ballHomeomorph_coe (g⁻¹*f).val.val (g⁻¹*f).property (Hyperbolic.ballOrigin (n+1))
  calc
    _ = f.val.val (0 : Euclidean (n+1)) := h1
    _ = g.val.val (g.val.val.symm (f.val.val (0 : Euclidean (n+1)))) := (g.val.val.apply_symm_apply _).symm
    _ = g.val.val ((ballMobiusOrigin (g⁻¹*f)).val : ExtendedEuclidean (n+1)) := congrArg g.val.val h2.symm
    _ = _ := (Hyperbolic.ballHomeomorph_coe g.val.val g.property (ballMobiusOrigin (g⁻¹*f))).symm

theorem ballMobiusOrigin_continuous : Continuous (ballMobiusOrigin (n := n)) := by
  rw [continuous_iff_continuousAt]
  intro g
  have hin : ContinuousAt (fun f : ballPreservingSubgroup n => g⁻¹*f) g :=
    (continuous_const.mul continuous_id).continuousAt
  have hout : ContinuousAt (ballMobiusOrigin (n := n)) (g⁻¹*g) := by
    simpa only [inv_mul_cancel] using (ballMobiusOrigin_continuousAt_one (n := n))
  have h := (Hyperbolic.ballHomeomorph g.val.val g.property).continuous.continuousAt.comp (hout.comp hin)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun f => ballMobiusOrigin_left_translate g f))

omit [NeZero n] in
theorem ballMobiusOrigin_pureTranslation_inv (a : Hyperbolic.unitBallDomain (n+1)) :
    ballMobiusOrigin ((pureTranslationBall a)⁻¹) = a := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  exact (Hyperbolic.ballHomeomorph_coe ((pureTranslation a)⁻¹ : ExtendedHomeomorph (n+1))
    (pureTranslation_preservesUnitBall a).inverse (Hyperbolic.ballOrigin (n+1))).trans (pureTranslation_inv_zero a)

omit [NeZero n] in
theorem ballMobiusOrigin_surjective : Function.Surjective (ballMobiusOrigin (n := n)) := by
  intro a
  exact ⟨(pureTranslationBall a)⁻¹,ballMobiusOrigin_pureTranslation_inv a⟩

/-- For the actual pure-translation subset and boundary topology. -/
def pureTranslationParameterHomeomorph (n : ℕ) [NeZero n] :
    Hyperbolic.unitBallDomain (n+1) ≃ₜ range (pureTranslationBall (n := n)) where
  toFun a := ⟨pureTranslationBall a,⟨a,rfl⟩⟩
  invFun f := ballMobiusOrigin f.val⁻¹
  left_inv a := ballMobiusOrigin_pureTranslation_inv a
  right_inv := by
    rintro ⟨f,⟨a,rfl⟩⟩
    apply Subtype.ext
    change pureTranslationBall (ballMobiusOrigin ((pureTranslationBall a)⁻¹)) = pureTranslationBall a
    rw [ballMobiusOrigin_pureTranslation_inv]
  continuous_toFun := pureTranslationBall_continuous.subtype_mk (fun a => ⟨a,rfl⟩)
  continuous_invFun := ballMobiusOrigin_continuous.comp (continuous_inv.comp continuous_subtype_val)

def orthogonalOperatorMap (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :
    Euclidean (n+1) →L[ℝ] Euclidean (n+1) := L.toLinearIsometry.toContinuousLinearMap

omit [NeZero n] in
theorem orthogonalOperatorMap_injective : Function.Injective (orthogonalOperatorMap (n := n)) := by
  intro L K he
  ext x : 1
  exact congrArg (fun f : Euclidean (n+1) →L[ℝ] Euclidean (n+1) => f x) he

abbrev orthogonalOperatorMetricSpace (n : ℕ) [NeZero n] : MetricSpace (Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :=
  MetricSpace.induced orthogonalOperatorMap orthogonalOperatorMap_injective inferInstance

local instance pureTranslationOrthogonalMetric : MetricSpace (Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :=
  orthogonalOperatorMetricSpace n

theorem orthogonalOperatorMap_isometry : Isometry (orthogonalOperatorMap (n := n)) :=
  MetricSpace.isometry_induced _ orthogonalOperatorMap_injective

def orthogonalBallMap (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) : ballPreservingSubgroup n :=
  orthogonalPureTranslationMap (L,Hyperbolic.ballOrigin (n+1))

omit [NeZero n] in
theorem orthogonalBallMap_coe (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :
    (orthogonalBallMap L).val.val = cartanLinearExtensionHom L := by
  change cartanLinearExtensionHom L * pureTranslation (Hyperbolic.ballOrigin (n+1)) = _
  rw [pureTranslation_origin,mul_one]

theorem orthogonalBallMap_isometry : Isometry (orthogonalBallMap (n := n)) := by
  apply Isometry.of_dist_eq
  intro L K
  rw [ballMobius_uniform_dist_eq_boundary]
  simp only [orthogonalBallMap_coe]
  change (⨆ x : Metric.sphere (0 : Euclidean (n+1)) 1, dist (L x.val) (K x.val)) =
    dist (orthogonalOperatorMap L) (orthogonalOperatorMap K)
  simp only [dist_eq_norm]
  have hr : range (fun x : Metric.sphere (0 : Euclidean (n+1)) 1 =>
      ‖L x.val-K x.val‖) =
      (fun x : Euclidean (n+1) => ‖(orthogonalOperatorMap L-orthogonalOperatorMap K) x‖) '' Metric.sphere 0 1 := by
    ext r
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  change sSup (range (fun x : Metric.sphere (0 : Euclidean (n+1)) 1 => ‖L x.val-K x.val‖)) = _
  rw [hr,ContinuousLinearMap.sSup_sphere_eq_norm]

open scoped Matrix.Norms.Frobenius

def orthogonalOperatorMatrixEquiv (n : ℕ) :
    (Euclidean (n+1) →L[ℝ] Euclidean (n+1)) ≃L[ℝ] Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Euclidean (n+1)) (F' := Euclidean (n+1))).symm.trans
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis)).toContinuousLinearEquiv

def orthogonalMatrixCoordinates (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := orthogonalOperatorMatrixEquiv n (orthogonalOperatorMap L)

omit [NeZero n] in
theorem orthogonalMatrixCoordinates_apply (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (i j : Fin (n+1)) :
    orthogonalMatrixCoordinates L i j = (L (EuclideanSpace.single j 1)) i := by
  change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis L.toLinearMap i j = _
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  rfl

theorem orthogonalMatrixCoordinates_isEmbedding : Topology.IsEmbedding (orthogonalMatrixCoordinates (n := n)) :=
  (orthogonalOperatorMatrixEquiv n).toHomeomorph.isEmbedding.comp orthogonalOperatorMap_isometry.isEmbedding

abbrev orthogonalFrobeniusMetricSpace (n : ℕ) [NeZero n] : MetricSpace (Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :=
  MetricSpace.induced orthogonalMatrixCoordinates orthogonalMatrixCoordinates_isEmbedding.injective inferInstance

theorem orthogonalFrobeniusMetricSpace_topology :
    (orthogonalFrobeniusMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (orthogonalOperatorMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  orthogonalMatrixCoordinates_isEmbedding.isInducing.eq_induced.symm

theorem orthogonalFrobeniusMetricSpace_dist (L K : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :
    @dist _ (orthogonalFrobeniusMetricSpace n).toDist L K =
      Real.sqrt (∑ i, ∑ j, (orthogonalMatrixCoordinates L i j-orthogonalMatrixCoordinates K i j)^2) := by
  change ‖orthogonalMatrixCoordinates L-orthogonalMatrixCoordinates K‖ = _
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply,Real.rpow_two,Real.norm_eq_abs,sq_abs]

omit [NeZero n] in
theorem orthogonalPureTranslationMap_mul
    (p : (Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) × Hyperbolic.unitBallDomain (n+1)) :
    orthogonalPureTranslationMap p = orthogonalBallMap p.1 * pureTranslationBall p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  change cartanLinearExtensionHom p.1 * pureTranslation p.2 = (orthogonalBallMap p.1).val.val * pureTranslation p.2
  rw [orthogonalBallMap_coe]

theorem orthogonalPureTranslationMap_continuous : Continuous (orthogonalPureTranslationMap (n := n)) := by
  have he : orthogonalPureTranslationMap (n := n) =
      fun p => orthogonalBallMap p.1 * pureTranslationBall p.2 := funext orthogonalPureTranslationMap_mul
  rw [he]
  exact (orthogonalBallMap_isometry.continuous.comp continuous_fst).mul
    (pureTranslationBall_continuous.comp continuous_snd)

omit [NeZero n] in
theorem orthogonalPureTranslationEquiv_symm_parameter (f : ballPreservingSubgroup n) :
    ((orthogonalPureTranslationEquiv n).symm f).2 = ballMobiusOrigin f⁻¹ := by
  let p := (orthogonalPureTranslationEquiv n).symm f
  have he : f.val.val = cartanLinearExtensionHom p.1 * pureTranslation p.2 := by
    have h := congrArg (fun k : ballPreservingSubgroup n => k.val.val)
      ((orthogonalPureTranslationEquiv n).apply_symm_apply f)
    exact h.symm
  have hp := pureTranslation_decomposition_parameter f.val.val p.1 p.2 he
  apply Subtype.ext
  apply OnePoint.coe_injective
  exact hp.symm.trans (Hyperbolic.ballHomeomorph_coe f⁻¹.val.val f⁻¹.property (Hyperbolic.ballOrigin (n+1))).symm

omit [NeZero n] in
theorem orthogonalPureTranslationEquiv_symm_orthogonal (f : ballPreservingSubgroup n) :
    orthogonalBallMap ((orthogonalPureTranslationEquiv n).symm f).1 =
      f * (pureTranslationBall ((orthogonalPureTranslationEquiv n).symm f).2)⁻¹ := by
  have he := (orthogonalPureTranslationEquiv n).apply_symm_apply f
  change orthogonalPureTranslationMap ((orthogonalPureTranslationEquiv n).symm f) = f at he
  rw [orthogonalPureTranslationMap_mul] at he
  calc
    _ = (orthogonalBallMap ((orthogonalPureTranslationEquiv n).symm f).1 *
      pureTranslationBall ((orthogonalPureTranslationEquiv n).symm f).2) *
        (pureTranslationBall ((orthogonalPureTranslationEquiv n).symm f).2)⁻¹ := by group
    _ = _ := by rw [he]

theorem orthogonalPureTranslationEquiv_symm_continuous :
    Continuous ((orthogonalPureTranslationEquiv n).symm) := by
  have ha : Continuous (fun f : ballPreservingSubgroup n => ((orthogonalPureTranslationEquiv n).symm f).2) := by
    have he : (fun f : ballPreservingSubgroup n => ((orthogonalPureTranslationEquiv n).symm f).2) =
        fun f => ballMobiusOrigin f⁻¹ := funext orthogonalPureTranslationEquiv_symm_parameter
    rw [he]
    exact ballMobiusOrigin_continuous.comp continuous_inv
  have hL : Continuous (fun f : ballPreservingSubgroup n => ((orthogonalPureTranslationEquiv n).symm f).1) := by
    apply orthogonalBallMap_isometry.comp_continuous_iff.mp
    have he : (orthogonalBallMap ∘ fun f : ballPreservingSubgroup n => ((orthogonalPureTranslationEquiv n).symm f).1) =
        fun f => f * (pureTranslationBall ((orthogonalPureTranslationEquiv n).symm f).2)⁻¹ :=
      funext orthogonalPureTranslationEquiv_symm_orthogonal
    rw [he]
    exact continuous_id.mul (pureTranslationBall_continuous.comp ha).inv
  exact hL.prodMk ha

def orthogonalPureTranslationHomeomorph (n : ℕ) [NeZero n] :
    ((Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) × Hyperbolic.unitBallDomain (n+1)) ≃ₜ ballPreservingSubgroup n where
  toEquiv := orthogonalPureTranslationEquiv n
  continuous_toFun := orthogonalPureTranslationMap_continuous
  continuous_invFun := orthogonalPureTranslationEquiv_symm_continuous

abbrev orthogonalFrobeniusProductTopology (n : ℕ) [NeZero n] :
    TopologicalSpace ((Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) × Hyperbolic.unitBallDomain (n+1)) :=
  @instTopologicalSpaceProd (Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (Hyperbolic.unitBallDomain (n+1))
    (orthogonalFrobeniusMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace inferInstance

/-- With the actual matrix Frobenius product topology. -/
def ballMobiusOrthogonalProductHomeomorph (n : ℕ) [NeZero n] :
    @Homeomorph (ballPreservingSubgroup n)
      ((Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) × Hyperbolic.unitBallDomain (n+1))
      (ballMobiusUniformMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (orthogonalFrobeniusProductTopology n) := by
  letI : TopologicalSpace ((Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) × Hyperbolic.unitBallDomain (n+1)) :=
    orthogonalFrobeniusProductTopology n
  exact {
    toEquiv := (orthogonalPureTranslationEquiv n).symm
    continuous_toFun := by
      unfold orthogonalFrobeniusProductTopology
      rw [orthogonalFrobeniusMetricSpace_topology]
      exact orthogonalPureTranslationEquiv_symm_continuous
    continuous_invFun := by
      unfold orthogonalFrobeniusProductTopology
      rw [orthogonalFrobeniusMetricSpace_topology]
      exact orthogonalPureTranslationMap_continuous }

omit [NeZero n] in
theorem orthogonalMatrixCoordinates_mem_orthogonalGroup (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :
    orthogonalMatrixCoordinates L ∈ Matrix.orthogonalGroup (Fin (n+1)) ℝ := by
  change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis L.toLinearMap ∈ Matrix.unitaryGroup (Fin (n+1)) ℝ
  exact L.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin (n+1)) ℝ)
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ)

def orthogonalMatrixGroupMap (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :
    Matrix.orthogonalGroup (Fin (n+1)) ℝ :=
  ⟨orthogonalMatrixCoordinates L,orthogonalMatrixCoordinates_mem_orthogonalGroup L⟩

omit [NeZero n] in
theorem orthogonalMatrixGroupMap_surjective : Function.Surjective (orthogonalMatrixGroupMap (n := n)) := by
  intro A
  refine ⟨Euclidean.orthogonalMatrixEquiv A.val A.property,?_⟩
  apply Subtype.ext
  change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis (Euclidean.orthogonalMatrixEquiv A.val A.property).toLinearMap
      = A.val
  exact Euclidean.orthogonalMatrixEquiv_toMatrix A.val A.property

theorem orthogonalMatrixGroupMap_isEmbedding : Topology.IsEmbedding (orthogonalMatrixGroupMap (n := n)) := by
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact orthogonalMatrixCoordinates_isEmbedding

def orthogonalMatrixCoordinateHomeomorph (n : ℕ) [NeZero n] :
    (Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) ≃ₜ Matrix.orthogonalGroup (Fin (n+1)) ℝ :=
  orthogonalMatrixGroupMap_isEmbedding.toHomeomorphOfSurjective orthogonalMatrixGroupMap_surjective

/-- The product parameterization also uses genuine orthogonal matrices in the standard basis. -/
def orthogonalMatrixBallHomeomorph (n : ℕ) [NeZero n] :
    ballPreservingSubgroup n ≃ₜ (Matrix.orthogonalGroup (Fin (n+1)) ℝ × Hyperbolic.unitBallDomain (n+1)) :=
  (orthogonalPureTranslationHomeomorph n).symm.trans
    ((orthogonalMatrixCoordinateHomeomorph n).prodCongr (Homeomorph.refl _))

end BoundaryMetric

end LowDimensionalTopology.Geometry.Inversive
