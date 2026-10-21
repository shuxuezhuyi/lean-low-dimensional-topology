/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.CommutatorGeometry
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

/-- A literal real rotation has the exact commutator trace determined by the true motion of its center. -/
theorem hRotationSL_commutator_trace (a b : ℝ) (hu : a^2+b^2=1)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (hRotationSL a b hu*B*(hRotationSL a b hu)⁻¹*B⁻¹).val/2=
      1+b^2*(Real.cosh (dist UpperHalfPlane.I (B•UpperHalfPlane.I))-1) := by
  have hm:=realGL_cosh_displacement (Matrix.SpecialLinearGroup.mapGL ℝ B)
  change Real.cosh (dist UpperHalfPlane.I (B•UpperHalfPlane.I))=
    (B 0 0^2+B 0 1^2+B 1 0^2+B 1 1^2)/(2*|B.val.det|) at hm
  rw [B.det_coe,abs_one,mul_one] at hm
  have hb : B 0 0*B 1 1-B 0 1*B 1 0-1=0 := by
    simpa only [Matrix.det_fin_two,sub_eq_zero] using B.det_coe
  rw [hSL_commutator_trace,hm]
  simp only [hRotationSL,Matrix.trace_fin_two,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  linear_combination (2-(B 0 0+B 1 1)^2/2)*hu+b^2*hb

/-- The elementary half-distance identity for the actual real hyperbolic cosine. -/
theorem real_cosh_eq_one_add_two_sinh_half_sq (x : ℝ) :
    Real.cosh x=1+2*Real.sinh (x/2)^2 := by
  have ha:=Real.cosh_two_mul (x/2)
  have hb:=Real.cosh_sq_sub_sinh_sq (x/2)
  rw [show 2*(x/2)=x by ring] at ha
  linarith

/--
The exact elliptic commutator trace uses the original actual center, its genuine movement,
and the genuine formulation rotation angle of the original transformation.
-/
theorem hElliptic_commutator_trace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    let v:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    Matrix.trace (A*B*A⁻¹*B⁻¹).val/2=1+2*Real.sinh (dist v (B•v)/2)^2*
      Real.sin (hEllipticRotationAngle A hA/2)^2 := by
  let v:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  obtain ⟨q,a,b,hu,hq,_hb,hrot⟩:=realSLMobius_elliptic_normal_form A hA
  let Bq:=q*B*q⁻¹
  have h:=hRotationSL_commutator_trace a b hu Bq
  have hcomm : hRotationSL a b hu*Bq*(hRotationSL a b hu)⁻¹*Bq⁻¹=q*(A*B*A⁻¹*B⁻¹)*q⁻¹ := by
    rw [←hrot]
    dsimp only [Bq]
    group
  have hmove : Bq•UpperHalfPlane.I=q•(B•v) := by
    rw [←hq]
    dsimp only [Bq]
    simp only [mul_smul,inv_smul_smul]
    rfl
  have hdist : dist UpperHalfPlane.I (Bq•UpperHalfPlane.I)=dist v (B•v) := by
    rw [hmove,←hq]
    exact (isometry_smul ℍ q).dist_eq v (B•v)
  have htr:=hSL_trace_conjugation A q
  rw [hrot] at htr
  have htr' : 2*a=Matrix.trace A.val := by simpa [hRotationSL,Matrix.trace_fin_two,two_mul] using htr
  have hspec:=(hEllipticRotationAngle_spec A hA).2.2.2
  have hsin : b^2=Real.sin (hEllipticRotationAngle A hA/2)^2 := by
    rw [←htr'] at hspec
    nlinarith [Real.sin_sq_add_cos_sq (hEllipticRotationAngle A hA/2)]
  rw [hcomm,hSL_trace_conjugation,hdist,hsin,real_cosh_eq_one_add_two_sinh_half_sq] at h
  dsimp only at h ⊢
  nlinarith

/--
For arbitrary original real conformal maps: the commutator is genuinely
hyperbolic and its actual translation length satisfies the exact center-angle formula.
-/
theorem hElliptic_commutator_translationLength
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusElliptic (realSLMobius A))
    (hB : B•hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)≠
      hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)) :
    let v:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    Mobius.MobiusHyperbolic (realSLMobius (A*B*A⁻¹*B⁻¹)) ∧
      Real.sinh (hTranslationLength (hSLIsometry (A*B*A⁻¹*B⁻¹))/4)=
        Real.sinh (dist v (B•v)/2)*Real.sin (hEllipticRotationAngle A hA/2) := by
  let v:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  let x:=Real.sinh (dist v (B•v)/2)*Real.sin (hEllipticRotationAngle A hA/2)
  have hv : 0<dist v (B•v) := dist_pos.mpr (Ne.symm hB)
  have hθ:=hElliptic_halfAngle_mem_Ioo A hA
  have hx : 0<x := mul_pos (Real.sinh_pos_iff.mpr (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have h:=hElliptic_commutator_trace A B hA
  dsimp only at h ⊢
  have h' : Matrix.trace (A*B*A⁻¹*B⁻¹).val/2=1+2*x^2 := by dsimp only [x,v];nlinarith [h]
  have ht : 2<Matrix.trace (A*B*A⁻¹*B⁻¹).val := by nlinarith [sq_pos_of_pos hx]
  have hh:=hSL_hyperbolic_of_two_lt_abs_trace (A*B*A⁻¹*B⁻¹) (lt_of_lt_of_le ht (le_abs_self _))
  have htcomm:=(realSLMobius_hyperbolic_iff _ hh.1.1).mp hh
  have hT:=hHyperbolic_translation_abs_trace _ hh.1.1 htcomm
  rw [abs_of_pos (by linarith : 0<Matrix.trace (A*B*A⁻¹*B⁻¹).val)] at hT
  have hdouble:=real_cosh_eq_one_add_two_sinh_half_sq
    (hTranslationLength (hSLIsometry (A*B*A⁻¹*B⁻¹))/2)
  rw [show hTranslationLength (hSLIsometry (A*B*A⁻¹*B⁻¹))/2/2=
    hTranslationLength (hSLIsometry (A*B*A⁻¹*B⁻¹))/4 by ring] at hdouble
  have hTp : 0<Real.sinh (hTranslationLength (hSLIsometry (A*B*A⁻¹*B⁻¹))/4) :=
    Real.sinh_pos_iff.mpr (by linarith [hHyperbolic_translationLength_pos _ hh.1.1 htcomm])
  refine ⟨hh,?_⟩
  change Real.sinh (hTranslationLength (hSLIsometry (A*B*A⁻¹*B⁻¹))/4)=x
  nlinarith


/-- The exact normalized parabolic commutator trace, for every original real second map. -/
theorem hTranslationSL_commutator_trace (t : ℝ) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (hTranslationSL t*B*(hTranslationSL t)⁻¹*B⁻¹).val=2+(t*B 1 0)^2 := by
  rw [hSL_commutator_trace]
  simp only [hTranslationSL,Matrix.trace_fin_two,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

/--
For arbitrary original real conformal transformations, with exactly the
source assumption that the parabolic first map and the second map have no common fixed point.
-/
theorem hParabolic_commutator_hyperbolic (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A))
    (hfix : ¬∃p:Mobius.ExtendedComplex,(realSLMobius A).val p=p ∧ (realSLMobius B).val p=p) :
    Mobius.MobiusHyperbolic (realSLMobius (A*B*A⁻¹*B⁻¹)) := by
  obtain ⟨q,t,ht,hrot⟩:=realSLMobius_parabolic_normal_form A hA
  let Bq:=q*B*q⁻¹
  have hprojA : realSLMobius (q*A*q⁻¹)=realSLMobius (hTranslationSL t) := by
    rcases hrot with he | he
    · rw [he]
    · rw [he,realSLMobius_neg]
  have hprojA' : realSLMobius q*realSLMobius A*(realSLMobius q)⁻¹=realSLMobius (hTranslationSL t) := by
    simpa only [map_mul,map_inv] using hprojA
  have hc : Bq 1 0≠0 := by
    intro he
    have hAi : (realSLMobius (q*A*q⁻¹)).val ∞=∞ := by
      rw [hprojA]
      apply (realSLMobius_fixed_infty_iff _).mpr
      simp [hTranslationSL]
    have hBi : (realSLMobius Bq).val ∞=∞ := (realSLMobius_fixed_infty_iff Bq).mpr he
    let p:Mobius.ExtendedComplex:=(realSLMobius q).val.symm ∞
    have hp : (realSLMobius q).val p=∞ := Equiv.apply_symm_apply _ _
    apply hfix
    exact ⟨p,(realSLMobius_conjugate_fixed_iff A q p).mp (by rw [hp];exact hAi),
      (realSLMobius_conjugate_fixed_iff B q p).mp (by rw [hp];exact hBi)⟩
  have hproj : realSLMobius ((q*A*q⁻¹)*Bq*(q*A*q⁻¹)⁻¹*Bq⁻¹)=
      realSLMobius (hTranslationSL t*Bq*(hTranslationSL t)⁻¹*Bq⁻¹) := by
    simp only [map_mul,map_inv,hprojA']
  have he:=hSL_abs_trace_congr hproj
  rw [show (q*A*q⁻¹)*Bq*(q*A*q⁻¹)⁻¹*Bq⁻¹=q*(A*B*A⁻¹*B⁻¹)*q⁻¹ by dsimp only [Bq];group,
    hSL_trace_conjugation] at he
  have htr:=hTranslationSL_commutator_trace t Bq
  have hgt : 2<Matrix.trace (hTranslationSL t*Bq*(hTranslationSL t)⁻¹*Bq⁻¹).val := by
    have hs : 0<(t*Bq 1 0)^2 := sq_pos_iff.mpr (mul_ne_zero ht hc)
    linarith
  apply hSL_hyperbolic_of_two_lt_abs_trace
  rw [he]
  exact lt_of_lt_of_le hgt (le_abs_self _)

end LowDimensionalTopology.Geometry.Hyperbolic
