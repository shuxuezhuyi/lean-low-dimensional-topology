/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.DisjointHyperbolicDirections
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.TransversalAngles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Interchanging two genuine isometries inverts their genuine commutator. -/
theorem hSL_commutator_swap (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    B*A*B⁻¹*A⁻¹=(A*B*A⁻¹*B⁻¹)⁻¹ := by group

/-- Simultaneous conjugation transports the entire genuine commutator. -/
theorem hSL_commutator_conjugation (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (q*A*q⁻¹)*(q*B*q⁻¹)*(q*A*q⁻¹)⁻¹*(q*B*q⁻¹)⁻¹=q*(A*B*A⁻¹*B⁻¹)*q⁻¹ := by group

/-- The original real determinant-one lifts satisfy the exact Fricke commutator trace identity. -/
theorem hSL_commutator_trace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A*B*A⁻¹*B⁻¹).val=(Matrix.trace A.val)^2+(Matrix.trace B.val)^2+
      (Matrix.trace (A*B).val)^2-Matrix.trace A.val*Matrix.trace B.val*Matrix.trace (A*B).val-2 := by
  have ha : A 0 0*A 1 1-A 0 1*A 1 0-1=0 := by
    simpa only [Matrix.det_fin_two,sub_eq_zero] using A.det_coe
  have hb : B 0 0*B 1 1-B 0 1*B 1 0-1=0 := by
    simpa only [Matrix.det_fin_two,sub_eq_zero] using B.det_coe
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  linear_combination ((B 0 0+B 1 1)^2-2*(B 0 0*B 1 1-B 0 1*B 1 0))*ha+
    ((A 0 0+A 1 1)^2-2)*hb

/-- The exact commutator trace of transformations fixing two pairs of actual axis endpoints. -/
theorem hSL_commutator_trace_axis_pairing
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine)
    (hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p)
    (hM : ∀p∈M.idealEndpoints,(realSLMobius B).val p=p) :
    Matrix.trace (A*B*A⁻¹*B⁻¹).val/2=
      1+2*((hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M)^2-
        (hAxisSignedSine A L)^2*(hAxisSignedSine B M)^2) := by
  have ha:=hSL_axis_signedSine_sq A L hL
  have hb:=hSL_axis_signedSine_sq B M hM
  have hp:=hSL_product_trace_axis_pairing A B L M hL hM
  change Matrix.trace (A*B).val/2=(Matrix.trace A.val/2)*(Matrix.trace B.val/2)+
    hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M at hp
  have he : Matrix.trace (A*B).val=2*((Matrix.trace A.val/2)*(Matrix.trace B.val/2)+
    hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M) := by linarith
  have hbase : Matrix.trace (A*B*A⁻¹*B⁻¹).val/2=
      1+2*((hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M)^2-
        ((Matrix.trace A.val/2)^2-1)*((Matrix.trace B.val/2)^2-1)) := by
    rw [hSL_commutator_trace,he]
    ring
  rwa [←ha,←hb] at hbase

/-- Actual ray angles and their actual supporting lines have the same squared cosine pairing. -/
theorem hAxisPairing_sq_eq_cos_angle {p : ℍ} (R S : HRayAt p) :
    (hAxisPairing R.supportLine S.supportLine)^2=(Real.cos (hInteriorAngleMeasure R S))^2 := by
  have hI:=halfPlane_inversiveProduct_eq_cos_acuteAngle R.supportLine S.supportLine p
    R.start_mem_support S.start_mem_support
  rw [halfPlane_inversiveProduct_eq_normal_product] at hI
  change |hAxisPairing R.supportLine S.supportLine|= _ at hI
  have hc:=acuteTangentAngle_cos_abs R.tangentVector S.tangentVector
  change Real.cos (min (hInteriorAngleMeasure R S) (Real.pi-hInteriorAngleMeasure R S))=
    |Real.cos (hInteriorAngleMeasure R S)| at hc
  rw [R.acuteAngle_eq_support S] at hc
  have he:=congrArg (fun x:ℝ=>x^2) (hI.trans hc)
  simpa only [sq_abs] using he

/-- The exact commutator trace at a genuine intersection, with the actual forward-ray angle. -/
theorem hHyperbolic_commutator_trace_intersection
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    {p : ℍ} (R S : HRayAt p)
    (hR : R.supportLine=hHyperbolicAxis A hA htA)
    (hS : S.supportLine=hHyperbolicAxis B hB htB) :
    Matrix.trace (A*B*A⁻¹*B⁻¹).val/2=
      1-2*(Real.sinh (hTranslationLength (hSLIsometry A)/2)*
        Real.sinh (hTranslationLength (hSLIsometry B)/2)*Real.sin (hInteriorAngleMeasure R S))^2 := by
  have hL : ∀x∈(hHyperbolicAxis A hA htA).idealEndpoints,(realSLMobius A).val x=x := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hM : ∀x∈(hHyperbolicAxis B hB htB).idealEndpoints,(realSLMobius B).val x=x := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have ha:=congrArg (fun x:ℝ=>x^2) (hAxisSignedSine_abs_eq_sinh_translation A hA htA)
  have hb:=congrArg (fun x:ℝ=>x^2) (hAxisSignedSine_abs_eq_sinh_translation B hB htB)
  rw [sq_abs] at ha hb
  have hc:=hAxisPairing_sq_eq_cos_angle R S
  rw [hR,hS] at hc
  have h:=hSL_commutator_trace_axis_pairing A B _ _ hL hM
  rw [mul_pow,mul_pow,ha,hb,hc] at h
  have hs:=Real.sin_sq_add_cos_sq (hInteriorAngleMeasure R S)
  linear_combination h+2*Real.sinh (hTranslationLength (hSLIsometry A)/2)^2*
    Real.sinh (hTranslationLength (hSLIsometry B)/2)^2*hs

/-- A nonelliptic genuine commutator forces the sharp axis-angle length bound. -/
theorem hHyperbolic_commutator_intersection_bound
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    {p : ℍ} (R S : HRayAt p)
    (hR : R.supportLine=hHyperbolicAxis A hA htA)
    (hS : S.supportLine=hHyperbolicAxis B hB htB)
    (hθ : 0<hInteriorAngleMeasure R S) (hθπ : hInteriorAngleMeasure R S<Real.pi)
    (hcomm : ¬Mobius.MobiusElliptic (realSLMobius (A*B*A⁻¹*B⁻¹))) :
    1≤Real.sinh (hTranslationLength (hSLIsometry A)/2)*
      Real.sinh (hTranslationLength (hSLIsometry B)/2)*Real.sin (hInteriorAngleMeasure R S) := by
  have h:=hHyperbolic_commutator_trace_intersection A B hA hB htA htB R S hR hS
  have hp : 0<Real.sinh (hTranslationLength (hSLIsometry A)/2)*
      Real.sinh (hTranslationLength (hSLIsometry B)/2)*Real.sin (hInteriorAngleMeasure R S) := by
    exact mul_pos (mul_pos
      (Real.sinh_pos_iff.mpr (by linarith [hHyperbolic_translationLength_pos A hA htA]))
      (Real.sinh_pos_iff.mpr (by linarith [hHyperbolic_translationLength_pos B hB htB])))
      (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)
  have hlt : Matrix.trace (A*B*A⁻¹*B⁻¹).val<2 := by nlinarith [sq_pos_of_pos hp]
  have hbound:=hSL_not_elliptic_abs_trace (A*B*A⁻¹*B⁻¹) hcomm
  have hneg : Matrix.trace (A*B*A⁻¹*B⁻¹).val≤ -2 := by
    rcases le_abs.mp hbound with hh | hh
    · linarith
    · linarith
  nlinarith


/-- Inverse maps have exactly the same actual metric translation length. -/
theorem hSL_translationLength_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hTranslationLength (hSLIsometry A⁻¹)=hTranslationLength (hSLIsometry A) := by
  have he : hDisplacement (hSLIsometry A⁻¹)=hDisplacement (hSLIsometry A) := by
    funext z
    rw [hSLIsometry_inverse,hDisplacement_inverse]
  unfold hTranslationLength
  rw [he]

/-- Genuine real conjugation preserves the actual metric translation-length infimum. -/
theorem hSL_translationLength_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hTranslationLength (hSLIsometry (q*A*q⁻¹))=hTranslationLength (hSLIsometry A) := by
  have he : hSLIsometry (q*A*q⁻¹)=((hSLIsometry q).symm.trans (hSLIsometry A)).trans (hSLIsometry q) := by
    apply IsometryEquiv.ext
    intro z
    change (q*A*q⁻¹)•z=q•(A•(q⁻¹•z))
    simp only [mul_smul]
  rw [he,hTranslationLength_conjugation]

/-- A hyperbolic transformation and its inverse have exactly the same genuine axis. -/
theorem hHyperbolicAxis_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (ht : 4 < (Matrix.trace A.val)^2) :
    hHyperbolicAxis A⁻¹ (by simpa only [map_inv] using inv_ne_one.mpr hA)
      (by rwa [hSL_trace_inverse])=hHyperbolicAxis A hA ht := by
  apply Eq.symm
  apply hHyperbolicAxis_unique
  rw [hHyperbolicAxis_idealEndpoints]
  ext p
  constructor
  · intro h
    change (realSLMobius A⁻¹).val p=p
    simpa only [map_inv] using Mobius.mobius_inv_fixed h
  · intro h
    change (realSLMobius A).val p=p
    have hi:=Mobius.mobius_inv_fixed h
    simpa only [map_inv,inv_inv] using hi

/--
The actual commutator translation length when the original axis and
its inverse conjugate cross, with the actual angle between their attractive rays.
-/
theorem hHyperbolic_commutator_crossed_conjugate_axes
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1)
    (htA : 4 < (Matrix.trace A.val)^2) {p : ℍ} (R S : HRayAt p)
    (hR : R.supportLine=hHyperbolicAxis A hA htA)
    (hS : S.supportLine=(hHyperbolicAxis A hA htA).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B))
    (hAttrR : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) R.idealEndpoint)
    (hAttrS : Mobius.MobiusAttractiveFixedPoint (realSLMobius (B*A⁻¹*B⁻¹)) S.idealEndpoint)
    (hθ : 0<hInteriorAngleMeasure R S) (hθπ : hInteriorAngleMeasure R S<Real.pi) :
    Mobius.MobiusHyperbolic (realSLMobius (A*B*A⁻¹*B⁻¹)) ∧
      Real.cosh (hTranslationLength (hSLIsometry (A*B*A⁻¹*B⁻¹))/2)=
        1+2*Real.sinh (hTranslationLength (hSLIsometry A)/2)^2*
          Real.cos (hInteriorAngleMeasure R S/2)^2 := by
  let C:=B*A⁻¹*B⁻¹
  have hi : realSLMobius A⁻¹≠1 := by simpa only [map_inv] using inv_ne_one.mpr hA
  have htI : 4 < (Matrix.trace (A⁻¹).val)^2 := by rwa [hSL_trace_inverse]
  have hC : realSLMobius C≠1:=hSL_nontrivial_conjugation A⁻¹ B hi
  have htC : 4 < (Matrix.trace C.val)^2 := by
    dsimp only [C]
    rwa [hSL_trace_conjugation,hSL_trace_inverse]
  have hcaxis : hHyperbolicAxis C hC htC=
      (hHyperbolicAxis A hA htA).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B) := by
    rw [hHyperbolicAxis_conjugation A⁻¹ B hi htI,hHyperbolicAxis_inverse A hA htA]
  have hpA : p∈(hHyperbolicAxis A hA htA).carrier := hR ▸ R.start_mem_support
  have hpC : p∈(hHyperbolicAxis C hC htC).carrier := by
    rw [hcaxis,←hS]
    exact S.start_mem_support
  have hTC : hTranslationLength (hSLIsometry C)=hTranslationLength (hSLIsometry A) := by
    dsimp only [C]
    rw [hSL_translationLength_conjugation,hSL_translationLength_inverse]
  obtain ⟨hh,htrace⟩:=hHyperbolic_intersecting_product_trace A C hA hC htA htC p hpA hpC
    R S hAttrR hAttrS hθ hθπ
  have he : A*C=A*B*A⁻¹*B⁻¹ := by dsimp only [C];group
  rw [he] at hh htrace
  rw [hTC] at htrace
  have htcomm:=(realSLMobius_hyperbolic_iff _ hh.1.1).mp hh
  rw [hHyperbolic_translation_abs_trace _ hh.1.1 htcomm] at htrace
  have hcos : Real.cos (hInteriorAngleMeasure R S)=2*Real.cos (hInteriorAngleMeasure R S/2)^2-1 := by
    have he:=Real.cos_two_mul (hInteriorAngleMeasure R S/2)
    rwa [show 2*(hInteriorAngleMeasure R S/2)=hInteriorAngleMeasure R S by ring] at he
  rw [hcos] at htrace
  have hid:=Real.cosh_sq_sub_sinh_sq (hTranslationLength (hSLIsometry A)/2)
  refine ⟨hh,?_⟩
  linear_combination htrace+hid


/-- The source commutator inversion identity in the actual original geometric Mobius group. -/
theorem geometric_commutator_swap (f g : Mobius.complexMobiusGroup) :
    g*f*g⁻¹*f⁻¹=(f*g*f⁻¹*g⁻¹)⁻¹ := by group

/-- The source simultaneous-conjugation identity in the actual original geometric Mobius group. -/
theorem geometric_commutator_conjugation (f g h : Mobius.complexMobiusGroup) :
    (h*f*h⁻¹)*(h*g*h⁻¹)*(h*f*h⁻¹)⁻¹*(h*g*h⁻¹)⁻¹=h*(f*g*f⁻¹*g⁻¹)*h⁻¹ := by group

end LowDimensionalTopology.Geometry.Hyperbolic
