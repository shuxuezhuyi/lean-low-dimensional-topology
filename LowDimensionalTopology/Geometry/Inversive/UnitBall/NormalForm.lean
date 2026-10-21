/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.NormalForm
public import LowDimensionalTopology.Geometry.Inversive.GeneralizedSpheres
public import Mathlib.Analysis.Normed.Module.RCLike.Real
/-!
# Unit-ball automorphisms and orthogonal reflections

The unit ball is the image of the Euclidean open ball in the one-point
compactification. Preservation of this actual set implies preservation of
its boundary and compact closure. A ball automorphism fixing zero is a global
orthogonal linear action. Every ball automorphism then factors into an
orthogonal action and a sphere or plane reflection orthogonal to the boundary.

Orthogonality has its geometric meaning: an intersection exists and the
radius normals have zero real inner product. The squared-radius criterion is
proved equivalent in dimension at least two. The finite inverse-centre
formulation explicitly excludes a zero centre, where division by its
squared norm would not describe an inverse point.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

def extendedUnitBall : Set (ExtendedEuclidean n) :=
  ((↑) : Euclidean n → ExtendedEuclidean n) '' Metric.ball (0 : Euclidean n) 1

def extendedClosedUnitBall : Set (ExtendedEuclidean n) :=
  ((↑) : Euclidean n → ExtendedEuclidean n) '' Metric.closedBall (0 : Euclidean n) 1

def extendedUnitSphere : Set (ExtendedEuclidean n) :=
  ((↑) : Euclidean n → ExtendedEuclidean n) '' Metric.sphere (0 : Euclidean n) 1

theorem isOpen_extendedUnitBall : IsOpen (extendedUnitBall : Set (ExtendedEuclidean n)) :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball

theorem isClosed_extendedClosedUnitBall :
    IsClosed (extendedClosedUnitBall : Set (ExtendedEuclidean n)) :=
  ((isCompact_closedBall (0 : Euclidean n) 1).image OnePoint.continuous_coe).isClosed

theorem closure_extendedUnitBall [NeZero n] :
    closure (extendedUnitBall : Set (ExtendedEuclidean n)) = extendedClosedUnitBall := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_extendedClosedUnitBall
    exact Set.image_mono Metric.ball_subset_closedBall
  · have he : Metric.closedBall (0 : Euclidean n) 1 = closure (Metric.ball 0 1) :=
      (closure_ball 0 one_ne_zero).symm
    change ((↑) : Euclidean n → ExtendedEuclidean n) '' Metric.closedBall (0 : Euclidean n) 1 ⊆ _
    rw [he]
    exact image_closure_subset_closure_image OnePoint.continuous_coe

theorem frontier_extendedUnitBall [NeZero n] :
    frontier (extendedUnitBall : Set (ExtendedEuclidean n)) = extendedUnitSphere := by
  rw [frontier, closure_extendedUnitBall, isOpen_extendedUnitBall.interior_eq]
  unfold extendedClosedUnitBall extendedUnitBall extendedUnitSphere
  rw [← Set.image_sdiff OnePoint.coe_injective, Metric.closedBall_sdiff_ball]

def PreservesUnitBall (f : ExtendedHomeomorph n) : Prop :=
  f '' extendedUnitBall = extendedUnitBall

theorem PreservesUnitBall.maps_sphere [NeZero n] {f : ExtendedHomeomorph n}
    (hf : PreservesUnitBall f) : f '' extendedUnitSphere = extendedUnitSphere := by
  rw [← frontier_extendedUnitBall, f.image_frontier, hf]

theorem PreservesUnitBall.maps_closedBall [NeZero n] {f : ExtendedHomeomorph n}
    (hf : PreservesUnitBall f) : f '' extendedClosedUnitBall = extendedClosedUnitBall := by
  rw [← closure_extendedUnitBall, f.image_closure, hf]

@[simp] theorem infty_not_mem_extendedClosedUnitBall :
    (∞ : ExtendedEuclidean n) ∉ extendedClosedUnitBall := by
  rintro ⟨x, _, hx⟩
  exact OnePoint.coe_ne_infty x hx

theorem PreservesUnitBall.pole_outside [NeZero n] {f : ExtendedHomeomorph n}
    (hf : PreservesUnitBall f) {c : Euclidean n} (hc : f c = ∞) : 1 < ‖c‖ := by
  by_contra h
  have hcm : (c : ExtendedEuclidean n) ∈ extendedClosedUnitBall :=
    ⟨c, by simpa using le_of_not_gt h, rfl⟩
  have hm : f (c : ExtendedEuclidean n) ∈ extendedClosedUnitBall := by
    rw [← hf.maps_closedBall]
    exact Set.mem_image_of_mem _ hcm
  rw [hc] at hm
  exact infty_not_mem_extendedClosedUnitBall hm

theorem PreservesUnitBall.norm_on_sphere [NeZero n] {f : ExtendedHomeomorph n}
    (hf : PreservesUnitBall f) (x : Euclidean n) (hx : ‖x‖ = 1) :
    f (x : ExtendedEuclidean n) ≠ ∞ ∧ ‖finiteEuclideanPart f x‖ = 1 := by
  have hxm : (x : ExtendedEuclidean n) ∈ extendedUnitSphere := ⟨x, by simpa using hx, rfl⟩
  have hm : f (x : ExtendedEuclidean n) ∈ extendedUnitSphere := by
    rw [← hf.maps_sphere]
    exact Set.mem_image_of_mem _ hxm
  obtain ⟨y, hy, he⟩ := hm
  refine ⟨by rw [← he]; exact OnePoint.coe_ne_infty _, ?_⟩
  rw [finiteEuclideanPart, ← he]
  simpa using hy
theorem generalMobius_ball_fixing_zero_fixes_infty [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (h0 : f (0 : Euclidean n) = (0 : Euclidean n)) : f ∞ = ∞ := by
  by_contra hinfty
  obtain ⟨c,k,hk,φ,rfl⟩ := generalMobius_nonAffine_normalForm f hf hinfty
  have hc : 1 < ‖c‖ := hB.pole_outside (nonAffineNormalForm_center c k hk φ)
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; linarith
  have hcpos : 0 < ‖c‖ := zero_lt_one.trans hc
  let v : Euclidean n := ‖c‖⁻¹ • c
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    exact inv_mul_cancel₀ hcpos.ne'
  have hnv : ‖-v‖ = 1 := by simpa only [norm_neg] using hv
  have hvc : v ≠ c := by intro h; rw [h] at hv; linarith
  have hnvc : -v ≠ c := by intro h; rw [h] at hnv; linarith
  have hfinite0 : finiteEuclideanPart (nonAffineNormalForm c k hk φ) 0 = 0 := by
    rw [finiteEuclideanPart,h0]
    rfl
  have hdist (x : Euclidean n) (hx : ‖x‖ = 1) (hxc : x ≠ c) :
      dist x c * ‖c‖ = k := by
    have hfx := (hB.norm_on_sphere x hx).2
    have hd := nonAffineNormalForm_dist c x 0 k hk φ hxc (Ne.symm hc0)
    rw [hfinite0, dist_zero_right, dist_zero_right, dist_zero_left, hfx, hx, mul_one] at hd
    simpa only [one_mul] using ((div_eq_iff (mul_ne_zero (dist_ne_zero.mpr hxc) hcpos.ne')).mp hd.symm).symm
  have hvd := hdist v hv hvc
  have hnvd := hdist (-v) hnv hnvc
  have heq : dist v c = dist (-v) c :=
    (mul_left_inj' hcpos.ne').mp (hvd.trans hnvd.symm)
  have hs := congrArg (fun t : ℝ ↦ t^2) heq
  rw [dist_eq_norm,dist_eq_norm,norm_sub_sq_real,norm_sub_sq_real,
    norm_neg,inner_neg_left] at hs
  have hiv : inner ℝ v c = ‖c‖ := by
    dsimp only [v]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  rw [hiv] at hs
  nlinarith

theorem exists_unit_euclidean_vector [NeZero n] : ∃ v : Euclidean n, ‖v‖ = 1 := by
  obtain ⟨w,hw⟩ := exists_ne (0 : Euclidean n)
  refine ⟨‖w‖⁻¹ • w, ?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hw)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

/-- as a global orthogonal linear action. -/
theorem ball_preserving_fix_zero_linearIsometry [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (h0 : f (0 : Euclidean n) = (0 : Euclidean n)) :
    ∃ L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n, f = cartanLinearExtensionHom L := by
  have hi := generalMobius_ball_fixing_zero_fixes_infty f hf hB h0
  obtain ⟨k,hk,φ,rfl⟩ := generalMobius_fixing_infty_normalForm f hf hi
  have he : k • φ 0 = (0 : Euclidean n) := OnePoint.coe_injective h0
  have hφ0 : φ 0 = 0 := (smul_eq_zero.mp he).resolve_left hk.ne'
  obtain ⟨v,hv⟩ := exists_unit_euclidean_vector (n := n)
  have hfv := (hB.norm_on_sphere v hv).2
  change ‖k • φ v‖ = 1 at hfv
  have hdist := extendedSimilarity_dist k hk φ v 0
  simp only [finiteEuclideanPart_extendedSimilarity,hφ0,smul_zero,
    dist_zero_right,hfv,hv,mul_one] at hdist
  have hk1 : k = 1 := hdist.symm
  subst k
  let F := φ.toRealAffineIsometryEquiv
  let L := F.linearIsometryEquiv
  have hL (x : Euclidean n) : L x = φ x := by
    have h := F.map_vadd 0 x
    change φ (x+0) = L x + φ 0 at h
    simpa only [add_zero,hφ0] using h.symm
  refine ⟨L, ?_⟩
  ext z
  induction z using OnePoint.rec with
  | infty => simp only [extendedSimilarity_infty,cartanLinearExtensionHom_infty]
  | coe x => rw [extendedSimilarity_coe,one_smul,cartanLinearExtensionHom_coe,hL]

theorem norm_sq_boundaryOrthogonal_inversion (c x : Euclidean n) (r : ℝ)
    (horth : ‖c‖ ^ 2 = 1 + r ^ 2) (hx : x ≠ c) :
    ‖inversion c r x‖ ^ 2 - 1 = r ^ 2 / ‖x-c‖ ^ 2 * (‖x‖ ^ 2 - 1) := by
  have hD : ‖x-c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
  rw [inversion_formula,div_pow,norm_add_sq_real,norm_smul,real_inner_smul_right,
    mul_pow,Real.norm_eq_abs,sq_abs,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real,horth] at hD ⊢
  rw [real_inner_comm c x]
  field_simp [hD]
  rw [real_inner_comm c x] at hD
  ring_nf at hD ⊢
  linear_combination -(r^2) * (mul_inv_cancel₀ hD)

theorem boundaryOrthogonal_inversion_maps_ball (c x : Euclidean n) (r : ℝ)
    (hr : 0 < r) (horth : ‖c‖ ^ 2 = 1 + r ^ 2) (hx : ‖x‖ < 1) :
    x ≠ c ∧ ‖inversion c r x‖ < 1 := by
  have hc : 1 < ‖c‖ := by nlinarith [sq_pos_of_pos hr,norm_nonneg c]
  have hxc : x ≠ c := by intro h; rw [h] at hx; linarith
  refine ⟨hxc, ?_⟩
  have hid := norm_sq_boundaryOrthogonal_inversion c x r horth hxc
  have hfac : 0 < r^2/‖x-c‖^2 :=
    div_pos (sq_pos_of_pos hr) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxc)))
  have hneg : ‖x‖^2-1 < 0 := by nlinarith [norm_nonneg x]
  have hprod := mul_neg_of_pos_of_neg hfac hneg
  nlinarith [norm_nonneg (inversion c r x)]

theorem sphereInversion_preservesUnitBall_of_boundaryOrthogonal (c : Euclidean n)
    (r : ℝ) (hr : 0 < r) (horth : ‖c‖ ^ 2 = 1 + r ^ 2) :
    PreservesUnitBall (sphereInversionHomeomorph c r hr.ne') := by
  have hmaps : Set.MapsTo (sphereInversionHomeomorph c r hr.ne') extendedUnitBall extendedUnitBall := by
    rintro z ⟨x,hx,rfl⟩
    have hnorm : ‖x‖ < 1 := by simpa using hx
    obtain ⟨hxc,hi⟩ := boundaryOrthogonal_inversion_maps_ball c x r hr horth hnorm
    refine ⟨inversion c r x, by simpa using hi, ?_⟩
    simp only [sphereInversionHomeomorph_apply,sphereInversion_coe c r hxc]
  apply Set.Subset.antisymm hmaps.image_subset
  intro z hz
  refine ⟨sphereInversionHomeomorph c r hr.ne' z, hmaps hz, ?_⟩
  exact sphereInversion_involutive c hr.ne' z

theorem PreservesUnitBall.mul {f g : ExtendedHomeomorph n}
    (hf : PreservesUnitBall f) (hg : PreservesUnitBall g) : PreservesUnitBall (f*g) := by
  change (f ∘ g) '' extendedUnitBall = extendedUnitBall
  rw [Set.image_comp,hg,hf]

theorem generalMobius_ball_pole_inverse_maps_zero [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (c : Euclidean n) (hc : f c = ∞) :
    f (unitInversion c : Euclidean n) = (0 : Euclidean n) := by
  have hcNorm := hB.pole_outside hc
  have hc0 : c ≠ 0 := by intro h; rw [h,norm_zero] at hcNorm; linarith
  let I := sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero
  have hI : IsReflection I := sphereInversion_isReflection 0 1 zero_lt_one
  have hfixed : Function.fixedPoints I = extendedUnitSphere :=
    fixedPoints_sphereInversion 0 1 zero_lt_one
  have hp : IsInversePair extendedUnitSphere (c : ExtendedEuclidean n)
      (unitInversion c : Euclidean n) := by
    refine ⟨I,hI,hfixed,?_⟩
    change sphereInversion 0 1 (c : ExtendedEuclidean n) = _
    rw [sphereInversion_coe 0 1 hc0,inversion_unit]
  have hpf := hp.image hf
  rw [hB.maps_sphere,hc] at hpf
  have hh := (isInversePair_iff_reflection_apply extendedUnitSphere I hI hfixed ∞
    (f (unitInversion c : Euclidean n))).mp hpf
  exact hh.symm

theorem boundaryOrthogonal_inversion_zero (c : Euclidean n) (r : ℝ)
    (hc : c ≠ 0) (horth : ‖c‖^2 = 1+r^2) :
    inversion c r 0 = unitInversion c := by
  rw [inversion_formula,zero_sub,norm_neg,div_pow]
  simp only [unitInversion,smul_neg]
  match_scalars
  field_simp [norm_ne_zero_iff.mpr hc]
  linarith

theorem generalMobius_ball_nonAffine_orthogonal_reflection [NeZero n]
    (f : ExtendedHomeomorph n) (hf : f ∈ generalMobiusGroup n)
    (hB : PreservesUnitBall f) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ r : ℝ, ∃ hr : 0 < r,
      ‖c‖^2 = 1+r^2 ∧ ∃ L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n,
        f = cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne' := by
  obtain ⟨c,k,hk,φ,he⟩ := generalMobius_nonAffine_normalForm f hf hinfty
  have hfc : f (c : ExtendedEuclidean n) = ∞ := by rw [he]; exact nonAffineNormalForm_center c k hk φ
  have hcNorm := hB.pole_outside hfc
  have hc0 : c ≠ 0 := by intro h; rw [h,norm_zero] at hcNorm; linarith
  have hrad : 0 < ‖c‖^2-1 := by nlinarith [norm_nonneg c]
  let r := Real.sqrt (‖c‖^2-1)
  have hr : 0 < r := Real.sqrt_pos.mpr hrad
  have horth : ‖c‖^2 = 1+r^2 := by dsimp only [r]; rw [Real.sq_sqrt hrad.le]; ring
  let S := sphereInversionHomeomorph c r hr.ne'
  have hS : IsReflection S := sphereInversion_isReflection c r hr
  have hSB : PreservesUnitBall S := sphereInversion_preservesUnitBall_of_boundaryOrthogonal c r hr horth
  have hFS : f*S ∈ generalMobiusGroup n := (generalMobiusGroup n).mul_mem hf hS.mem_generalMobiusGroup
  have hFS0 : (f*S) (0 : Euclidean n) = (0 : Euclidean n) := by
    change f (sphereInversion c r (0 : Euclidean n)) = _
    rw [sphereInversion_coe c r (Ne.symm hc0),boundaryOrthogonal_inversion_zero c r hc0 horth]
    exact generalMobius_ball_pole_inverse_maps_zero f hf hB c hfc
  obtain ⟨L,hL⟩ := ball_preserving_fix_zero_linearIsometry (f*S) hFS (hB.mul hSB) hFS0
  refine ⟨c,r,hr,horth,L,?_⟩
  change f = cartanLinearExtensionHom L * S
  calc
    _ = (f*S)*S⁻¹ := by group
    _ = _ := by rw [hL,hS.inv_eq]

theorem generalMobius_ball_commutes_unitInversion [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f) :
    f * sphereInversionHomeomorph 0 1 one_ne_zero =
      sphereInversionHomeomorph 0 1 one_ne_zero * f := by
  let I := sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero
  have hI : IsReflection I := sphereInversion_isReflection 0 1 zero_lt_one
  have hfixed : Function.fixedPoints I = extendedUnitSphere := fixedPoints_sphereInversion 0 1 zero_lt_one
  have he : f*I*f⁻¹ = I := (generalMobius_conjugate_isReflection hf hI).eq_of_fixedPoints hI (by
    rw [fixedPoints_homeomorph_conjugation,hfixed,hB.maps_sphere])
  change f*I=I*f
  calc
    _ = (f*I*f⁻¹)*f := by group
    _ = _ := by rw [he]

theorem generalMobius_ball_fixing_infty_fixes_zero [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f) (hi : f ∞ = ∞) :
    f (0 : Euclidean n) = (0 : Euclidean n) := by
  have he := congrArg (fun g : ExtendedHomeomorph n ↦ g ∞)
    (generalMobius_ball_commutes_unitInversion f hf hB)
  change f (sphereInversion 0 1 ∞) = sphereInversion 0 1 (f ∞) at he
  simpa only [sphereInversion_infty,hi] using he

theorem cartanLinearExtension_preservesUnitBall (L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) :
    PreservesUnitBall (cartanLinearExtensionHom L) := by
  apply Set.Subset.antisymm
  · rintro z ⟨y,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨L x,by simpa only [Metric.mem_ball,dist_zero_right,L.norm_map] using hx,rfl⟩
  · rintro z ⟨y,hy,rfl⟩
    refine ⟨(L.symm y : Euclidean n),⟨L.symm y,?_,rfl⟩,?_⟩
    · simpa only [Metric.mem_ball,dist_zero_right,L.symm.norm_map] using hy
    · rw [cartanLinearExtensionHom_coe,L.apply_symm_apply]

theorem planeReflection_preservesUnitBall_zero (a : Euclidean n) (ha : a ≠ 0) :
    PreservesUnitBall (planeReflectionHomeomorph a 0 ha) := by
  rw [← cartanLinearExtension_plane]
  exact cartanLinearExtension_preservesUnitBall _

def IsUnitBoundaryOrthogonalReflection (s : ExtendedHomeomorph n) : Prop :=
  (∃ a : Euclidean n, ∃ ha : a ≠ 0, s = planeReflectionHomeomorph a 0 ha) ∨
  (∃ c : Euclidean n, ∃ r : ℝ, ∃ hr : 0 < r,
    ‖c‖^2 = 1+r^2 ∧ s = sphereInversionHomeomorph c r hr.ne')

theorem IsUnitBoundaryOrthogonalReflection.isReflection {s : ExtendedHomeomorph n}
    (hs : IsUnitBoundaryOrthogonalReflection s) : IsReflection s := by
  rcases hs with ⟨a,ha,rfl⟩ | ⟨c,r,hr,_,rfl⟩
  · exact planeReflection_isReflection a 0 ha
  · exact sphereInversion_isReflection c r hr

theorem IsUnitBoundaryOrthogonalReflection.preservesUnitBall {s : ExtendedHomeomorph n}
    (hs : IsUnitBoundaryOrthogonalReflection s) : PreservesUnitBall s := by
  rcases hs with ⟨a,ha,rfl⟩ | ⟨c,r,hr,horth,rfl⟩
  · exact planeReflection_preservesUnitBall_zero a ha
  · exact sphereInversion_preservesUnitBall_of_boundaryOrthogonal c r hr horth

/-- planes through zero are included as generalized spheres. -/
theorem ball_preserving_linearIsometry_mul_orthogonal_reflection [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f) :
    ∃ L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n, ∃ s : ExtendedHomeomorph n,
      IsUnitBoundaryOrthogonalReflection s ∧ f = cartanLinearExtensionHom L * s := by
  by_cases hi : f ∞ = ∞
  · obtain ⟨L,hL⟩ := ball_preserving_fix_zero_linearIsometry f hf hB (generalMobius_ball_fixing_infty_fixes_zero f
      hf hB hi)
    obtain ⟨a,ha⟩ := exists_ne (0 : Euclidean n)
    let P := planeReflectionHomeomorph a 0 ha
    have hP : IsReflection P := planeReflection_isReflection a 0 ha
    refine ⟨L*cartanPlaneLinearIsometry a,P,Or.inl ⟨a,ha,rfl⟩,?_⟩
    rw [map_mul,cartanLinearExtension_plane]
    change f=cartanLinearExtensionHom L*P*P
    rw [← hL]
    calc
      _ = f*P*P⁻¹ := by group
      _ = _ := by rw [hP.inv_eq]
  · obtain ⟨c,r,hr,horth,L,hL⟩ := generalMobius_ball_nonAffine_orthogonal_reflection f hf hB hi
    exact ⟨L,sphereInversionHomeomorph c r hr.ne',Or.inr ⟨c,r,hr,horth,rfl⟩,hL⟩

theorem planeReflection_preservesUnitBall_iff [NeZero n] (a : Euclidean n) (t : ℝ)
    (ha : a ≠ 0) : PreservesUnitBall (planeReflectionHomeomorph a t ha) ↔ t = 0 := by
  constructor
  · intro hB
    have h0 := generalMobius_ball_fixing_infty_fixes_zero (planeReflectionHomeomorph a t ha)
      (planeReflection_isReflection a t ha).mem_generalMobiusGroup hB rfl
    have hfin : planeReflectionFinite a t 0 = 0 := OnePoint.coe_injective h0
    have ht := (planeReflectionFinite_fixed_iff a t ha 0).mp hfin
    simpa only [inner_zero_left] using ht.symm
  · rintro rfl
    exact planeReflection_preservesUnitBall_zero a ha

theorem inversion_zero_eq_unitInversion_iff (c : Euclidean n) (r : ℝ) (hc : c ≠ 0) :
    inversion c r 0 = unitInversion c ↔ ‖c‖^2 = 1+r^2 := by
  constructor
  · intro he
    rw [inversion_formula,zero_sub,norm_neg,div_pow,unitInversion] at he
    have hsmul : (1-r^2/‖c‖^2) • c = (‖c‖^2)⁻¹ • c := by
      calc
        _ = c+(r^2/‖c‖^2) • (-c) := by module
        _ = _ := he
    have hs := smul_left_injective ℝ hc hsmul
    field_simp [norm_ne_zero_iff.mpr hc] at hs
    nlinarith
  · exact boundaryOrthogonal_inversion_zero c r hc

theorem sphereInversion_preservesUnitBall_iff [NeZero n] (c : Euclidean n) (r : ℝ)
    (hr : 0 < r) : PreservesUnitBall (sphereInversionHomeomorph c r hr.ne') ↔
      ‖c‖^2 = 1+r^2 := by
  constructor
  · intro hB
    have hcnorm := hB.pole_outside (by
      change sphereInversion c r (c : ExtendedEuclidean n) = ∞
      exact sphereInversion_center c r)
    have hc0 : c ≠ 0 := by intro h; rw [h,norm_zero] at hcnorm; linarith
    have hcomm := generalMobius_ball_commutes_unitInversion
      (sphereInversionHomeomorph c r hr.ne')
      (sphereInversion_isReflection c r hr).mem_generalMobiusGroup hB
    have he := congrArg (fun g : ExtendedHomeomorph n ↦ g ∞) hcomm
    change sphereInversion c r (sphereInversion 0 1 ∞) =
      sphereInversion 0 1 (sphereInversion c r ∞) at he
    rw [sphereInversion_infty,sphereInversion_infty,
      sphereInversion_coe c r (Ne.symm hc0),sphereInversion_coe 0 1 hc0,inversion_unit] at he
    exact (inversion_zero_eq_unitInversion_iff c r hc0).mp (OnePoint.coe_injective he)
  · exact sphereInversion_preservesUnitBall_of_boundaryOrthogonal c r hr

theorem finiteEuclideanPart_linear_mul (L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (f : ExtendedHomeomorph n) (x : Euclidean n) :
    finiteEuclideanPart (cartanLinearExtensionHom L * f) x = L (finiteEuclideanPart f x) := by
  unfold finiteEuclideanPart
  change ((cartanLinearExtensionHom L) (f x)).elim 0 id = L ((f x).elim 0 id)
  induction h : f (x : ExtendedEuclidean n) using OnePoint.rec with
  | infty => exact L.map_zero.symm
  | coe y => rfl

theorem isometricSphere_linear_mul (L : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (f : ExtendedHomeomorph n) :
    isometricSphere (cartanLinearExtensionHom L*f) = isometricSphere f := by
  ext x
  have hreg : (cartanLinearExtensionHom L*f) (x : ExtendedEuclidean n) ≠ ∞ ↔
      f (x : ExtendedEuclidean n) ≠ ∞ := by
    change (cartanLinearExtensionHom L) (f x) ≠ ∞ ↔ _
    rw [← cartanLinearExtensionHom_infty L]
    exact (cartanLinearExtensionHom L).injective.ne_iff
  simp only [isometricSphere,Set.mem_ofPred_eq,hreg,finiteEuclideanPart_linear_mul,L.isometry.dist_eq]

theorem sphereInversionHomeomorph_isometricSphere [NeZero n] (c : Euclidean n)
    (r : ℝ) (hr : 0 < r) :
    isometricSphere (sphereInversionHomeomorph c r hr.ne') = Metric.sphere c r := by
  have hscale (x : Euclidean n) (hx : x ≠ c) :
      Tendsto (fun y : Euclidean n ↦
        dist (finiteEuclideanPart (sphereInversionHomeomorph c r hr.ne') y)
          (finiteEuclideanPart (sphereInversionHomeomorph c r hr.ne') x) / dist y x)
        (𝓝[≠] x) (𝓝 (r^2/dist x c^2)) := by
    apply (sphereInversion_scale_limit r hx).congr'
    filter_upwards [(eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds] with y hy
    simp only [finiteEuclideanPart,sphereInversionHomeomorph_apply,
      sphereInversion_coe c r hy,sphereInversion_coe c r hx]
    rfl
  ext x
  constructor
  · rintro ⟨hx,hs⟩
    have hxc : x ≠ c := by intro he; subst x; exact hx (sphereInversion_center c r)
    have hd : dist x c^2 ≠ 0 := pow_ne_zero 2 (dist_ne_zero.mpr hxc)
    have he := (div_eq_one_iff_eq hd).mp (tendsto_nhds_unique (hscale x hxc) hs)
    change dist x c = r
    nlinarith [dist_nonneg (x := x) (y := c)]
  · intro hx
    change dist x c = r at hx
    have hxc : x ≠ c := dist_pos.mp (hx ▸ hr)
    refine ⟨?_, ?_⟩
    · rw [sphereInversionHomeomorph_apply,sphereInversion_coe c r hxc]
      exact OnePoint.coe_ne_infty _
    · simpa only [hx,div_self (pow_ne_zero 2 hr.ne')] using hscale x hxc

/-- For a ball automorphism its actual isometric sphere is boundary-orthogonal. -/
theorem generalMobius_ball_isometricSphere_orthogonal [NeZero n]
    (f : ExtendedHomeomorph n) (hf : f ∈ generalMobiusGroup n)
    (hB : PreservesUnitBall f) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ r : ℝ, 0 < r ∧
      isometricSphere f = Metric.sphere c r ∧ ‖c‖^2 = 1+r^2 := by
  obtain ⟨c,r,hr,horth,L,he⟩ := generalMobius_ball_nonAffine_orthogonal_reflection f hf hB hinfty
  refine ⟨c,r,hr,?_,horth⟩
  rw [he,isometricSphere_linear_mul,sphereInversionHomeomorph_isometricSphere c r hr]

theorem sphereInversion_inverse_center_eq_zero_iff (c : Euclidean n) (r : ℝ)
    (hr : 0 < r) (hc : c ≠ 0) :
    sphereInversion c r (unitInversion c : Euclidean n) = (0 : Euclidean n) ↔
      ‖c‖^2 = 1+r^2 := by
  have hi := sphereInversion_involutive c hr.ne'
  have he : sphereInversion c r (unitInversion c : Euclidean n) = (0 : Euclidean n) ↔
      sphereInversion c r (0 : Euclidean n) = (unitInversion c : Euclidean n) := by
    constructor
    · intro h
      have hh := congrArg (sphereInversion c r) h
      exact hh.symm.trans (hi _)
    · intro h
      have hh := congrArg (sphereInversion c r) h
      exact hh.symm.trans (hi _)
  rw [he,sphereInversion_coe c r (Ne.symm hc),OnePoint.coe_eq_coe]
  exact inversion_zero_eq_unitInversion_iff c r hc

theorem exists_orthogonal_unit_vector (hn : 2 ≤ n) (c : Euclidean n) (hc : c ≠ 0) :
    ∃ w : Euclidean n, ‖w‖ = 1 ∧ inner ℝ c w = 0 := by
  let K := (ℝ ∙ c)ᗮ
  have hd := (ℝ ∙ c).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hc,finrank_euclideanSpace_fin] at hd
  have hpos : 0 < Module.finrank ℝ K := by dsimp only [K]; omega
  have : Nontrivial K := Module.finrank_pos_iff.mp hpos
  obtain ⟨w,hw⟩ := exists_ne (0 : K)
  have hw0 : (w : Euclidean n) ≠ 0 := by exact_mod_cast hw
  have hcw : inner ℝ c (w : Euclidean n) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  refine ⟨‖(w : Euclidean n)‖⁻¹ • (w : Euclidean n), ?_, ?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hw0)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  · rw [real_inner_smul_right,hcw,mul_zero]

theorem sphere_boundary_inner_iff (c x : Euclidean n) (r : ℝ)
    (hx : ‖x‖ = 1) (hs : dist x c = r) :
    inner ℝ x (x-c) = 0 ↔ ‖c‖^2 = 1+r^2 := by
  have hdist := norm_sub_sq_real x c
  rw [← dist_eq_norm,hs,hx] at hdist
  rw [inner_sub_right,real_inner_self_eq_norm_sq,hx]
  constructor <;> intro h <;> nlinarith

/-- Two spheres meet with perpendicular radius normals; all intersections then have this property. -/
def UnitSphereOrthogonal (c : Euclidean n) (r : ℝ) : Prop :=
  ∃ x : Euclidean n, ‖x‖ = 1 ∧ dist x c = r ∧ inner ℝ x (x-c) = 0

theorem UnitSphereOrthogonal.norm_sq {c : Euclidean n} {r : ℝ}
    (h : UnitSphereOrthogonal c r) : ‖c‖^2 = 1+r^2 := by
  obtain ⟨x,hx,hs,hi⟩ := h
  exact (sphere_boundary_inner_iff c x r hx hs).mp hi

theorem UnitSphereOrthogonal.inner_at_intersection {c : Euclidean n} {r : ℝ}
    (h : UnitSphereOrthogonal c r) (x : Euclidean n) (hx : ‖x‖ = 1) (hs : dist x c = r) :
    inner ℝ x (x-c) = 0 := (sphere_boundary_inner_iff c x r hx hs).mpr h.norm_sq

theorem unitSphereOrthogonal_iff_norm_sq (hn : 2 ≤ n) (c : Euclidean n)
    (r : ℝ) (hr : 0 < r) : UnitSphereOrthogonal c r ↔ ‖c‖^2 = 1+r^2 := by
  constructor
  · exact Inversive.UnitSphereOrthogonal.norm_sq
  · intro horth
    have hcNorm : 1 < ‖c‖ := by nlinarith [sq_pos_of_pos hr,norm_nonneg c]
    have hc0 : c ≠ 0 := by intro h; rw [h,norm_zero] at hcNorm; linarith
    have hC : 1 < ‖c‖^2 := by nlinarith [sq_pos_of_pos hr]
    have hCpos : 0 < ‖c‖^2 := zero_lt_one.trans hC
    obtain ⟨w,hw,hcw⟩ := exists_orthogonal_unit_vector hn c hc0
    let a : Euclidean n := (‖c‖^2)⁻¹ • c
    let q : ℝ := Real.sqrt (1-(‖c‖^2)⁻¹)
    have hq : 0 ≤ 1-(‖c‖^2)⁻¹ := by
      have hi := (inv_lt_one₀ hCpos).mpr hC
      linarith
    have haNorm : ‖a‖^2 = (‖c‖^2)⁻¹ := by
      simp only [a,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      field_simp
    have hac : inner ℝ a c = 1 := by
      dsimp only [a]
      rw [real_inner_smul_left,real_inner_self_eq_norm_sq,inv_mul_cancel₀ hCpos.ne']
    have haw : inner ℝ a w = 0 := by
      dsimp only [a]
      rw [real_inner_smul_left,hcw,mul_zero]
    let x := a+q•w
    have hxNormSq : ‖x‖^2 = 1 := by
      dsimp only [x]
      rw [norm_add_sq_real,real_inner_smul_right,haw,mul_zero,mul_zero,add_zero,haNorm]
      rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,hw,one_pow,mul_one]
      dsimp only [q]
      rw [Real.sq_sqrt hq]
      ring
    have hxNorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
    have hxc : inner ℝ x c = 1 := by
      dsimp only [x]
      rw [inner_add_left,hac,real_inner_smul_left,real_inner_comm c w,hcw,mul_zero,add_zero]
    have hsSq : dist x c^2 = r^2 := by
      rw [dist_eq_norm,norm_sub_sq_real,hxNormSq,hxc,horth]
      ring
    have hs : dist x c = r := by nlinarith [dist_nonneg (x := x) (y := c)]
    exact ⟨x,hxNorm,hs,(sphere_boundary_inner_iff c x r hxNorm hs).mpr horth⟩

theorem sphere_orthogonal_iff_inversion_preserves_ball (hn : 2 ≤ n) (c : Euclidean n) (r : ℝ) (hr : 0 < r) :
    UnitSphereOrthogonal c r ↔ PreservesUnitBall (sphereInversionHomeomorph c r hr.ne') := by
  have : NeZero n := ⟨by omega⟩
  rw [unitSphereOrthogonal_iff_norm_sq hn c r hr,sphereInversion_preservesUnitBall_iff c r hr]

theorem generalMobius_ball_isometricSphere_geometrically_orthogonal (hn : 2 ≤ n)
    (f : ExtendedHomeomorph n) (hf : f ∈ generalMobiusGroup n)
    (hB : PreservesUnitBall f) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ r : ℝ, 0 < r ∧
      isometricSphere f = Metric.sphere c r ∧ UnitSphereOrthogonal c r := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨c,r,hr,hs,horth⟩ := generalMobius_ball_isometricSphere_orthogonal f hf hB hinfty
  exact ⟨c,r,hr,hs,(unitSphereOrthogonal_iff_norm_sq hn c r hr).mpr horth⟩

theorem sphere_orthogonal_iff_inversion_unitInversion_center_eq_zero (hn : 2 ≤ n) (c : Euclidean n) (r : ℝ)
    (hr : 0 < r) (hc : c ≠ 0) :
    UnitSphereOrthogonal c r ↔
      sphereInversion c r (unitInversion c : Euclidean n) = (0 : Euclidean n) := by
  rw [unitSphereOrthogonal_iff_norm_sq hn c r hr,sphereInversion_inverse_center_eq_zero_iff c r hr hc]

theorem sphere_orthogonal_iff_inversion_zero_eq_unitInversion_center (hn : 2 ≤ n) (c : Euclidean n) (r : ℝ)
    (hr : 0 < r) (hc : c ≠ 0) :
    UnitSphereOrthogonal c r ↔
      sphereInversion c r (0 : Euclidean n) = (unitInversion c : Euclidean n) := by
  rw [unitSphereOrthogonal_iff_norm_sq hn c r hr,
    sphereInversion_coe c r (Ne.symm hc),OnePoint.coe_eq_coe]
  exact (inversion_zero_eq_unitInversion_iff c r hc).symm

/-- A plane meets the unit sphere with its normal perpendicular to a radius normal. -/
def UnitPlaneOrthogonal (a : Euclidean n) (t : ℝ) : Prop :=
  ∃ x : Euclidean n, ‖x‖ = 1 ∧ inner ℝ x a = t ∧ inner ℝ x a = 0

theorem unitPlaneOrthogonal_iff (hn : 2 ≤ n) (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    UnitPlaneOrthogonal a t ↔ t = 0 := by
  constructor
  · rintro ⟨x,_,ht,h0⟩
    exact ht.symm.trans h0
  · rintro rfl
    obtain ⟨w,hw,hwa⟩ := exists_orthogonal_unit_vector hn a ha
    have hw0 : inner ℝ w a = 0 := by rw [real_inner_comm a w]; exact hwa
    exact ⟨w,hw,hw0,hw0⟩

theorem planeReflection_preservesUnitBall_iff_geometric (hn : 2 ≤ n)
    (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    PreservesUnitBall (planeReflectionHomeomorph a t ha) ↔ UnitPlaneOrthogonal a t := by
  have : NeZero n := ⟨by omega⟩
  rw [planeReflection_preservesUnitBall_iff a t ha,unitPlaneOrthogonal_iff hn a t ha]

theorem IsUnitBoundaryOrthogonalReflection.geometric (hn : 2 ≤ n)
    {s : ExtendedHomeomorph n} (hs : IsUnitBoundaryOrthogonalReflection s) :
    (∃ a : Euclidean n, ∃ ha : a ≠ 0,
      s = planeReflectionHomeomorph a 0 ha ∧ UnitPlaneOrthogonal a 0) ∨
    (∃ c : Euclidean n, ∃ r : ℝ, ∃ hr : 0 < r,
      s = sphereInversionHomeomorph c r hr.ne' ∧ UnitSphereOrthogonal c r) := by
  rcases hs with ⟨a,ha,rfl⟩ | ⟨c,r,hr,horth,rfl⟩
  · exact Or.inl ⟨a,ha,rfl,(unitPlaneOrthogonal_iff hn a 0 ha).mpr rfl⟩
  · exact Or.inr ⟨c,r,hr,rfl,(unitSphereOrthogonal_iff_norm_sq hn c r hr).mpr horth⟩

theorem ball_preserving_fix_zero_orthogonal_matrix [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hB : PreservesUnitBall f)
    (h0 : f (0 : Euclidean n) = (0 : Euclidean n)) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, Auxiliary.Algebra.OrthogonalMatrix A ∧
      ∀ x : Euclidean n, f (x : ExtendedEuclidean n) =
        ((WithLp.toLp 2 (Matrix.vecMul x.ofLp A) : Euclidean n) : ExtendedEuclidean n) := by
  obtain ⟨L,rfl⟩ := ball_preserving_fix_zero_linearIsometry f hf hB h0
  refine ⟨Euclidean.isometryRowMatrix L,Euclidean.isometryRowMatrix_orthogonal L,?_⟩
  intro x
  rw [cartanLinearExtensionHom_coe,Euclidean.isometryRowMatrix_apply]

end LowDimensionalTopology.Geometry.Inversive
