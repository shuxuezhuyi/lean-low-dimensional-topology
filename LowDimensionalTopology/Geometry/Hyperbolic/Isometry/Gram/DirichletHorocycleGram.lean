/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RationalRealLocus
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeParabolicPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementFunctions
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Polynomial
open scoped Topology OnePoint UpperHalfPlane MatrixGroups Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A metric Gram expression detects the ideal circumcircle degeneration of three actual hyperbolic-plane points. -/
def horocycleMetricGram (a b c : ℍ) : ℝ :=
  4*(Real.cosh (dist a b)-1)*(Real.cosh (dist a c)-1)-
    (Real.cosh (dist a b)+Real.cosh (dist a c)-Real.cosh (dist b c)-1)^2

theorem horocycleMetricGram_realGL_smul (g : GL (Fin 2) ℝ) (a b c : ℍ) :
    horocycleMetricGram (g • a) (g • b) (g • c)=horocycleMetricGram a b c := by
  simp only [horocycleMetricGram,(realGL_isometry g).dist_eq]

theorem horocycleMetricGram_eq_zero_of_same_im (a b c : ℍ) (hb : b.im=a.im) (hc : c.im=a.im) :
    horocycleMetricGram a b c=0 := by
  rw [horocycleMetricGram,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',hb,hc]
  field_simp [a.im_ne_zero]
  ring

/-- Three actual points on a genuine intrinsic horocycle have zero metric Gram expression. -/
theorem horocycleMetricGram_eq_zero_of_horocycle {ξ : Mobius.ExtendedComplex} {S : Set ℍ}
    (hS : IsHHorocycleAt ξ S) {a b c : ℍ} (ha : a∈S) (hb : b∈S) (hc : c∈S) :
    horocycleMetricGram a b c=0 := by
  obtain ⟨g,hg,rfl⟩:=exists_hParabolicChart ξ hS.center_mem_idealBoundary
  obtain ⟨t,_ht,rfl⟩:=(isHHorocycleAt_chart_iff g hg S).mp hS
  obtain ⟨a0,ha0,rfl⟩:=ha
  obtain ⟨b0,hb0,rfl⟩:=hb
  obtain ⟨c0,hc0,rfl⟩:=hc
  rw [horocycleMetricGram_realGL_smul]
  exact horocycleMetricGram_eq_zero_of_same_im a0 b0 c0 (hb0.trans ha0.symm) (hc0.trans ha0.symm)

/-- The actual quadratic governing displacement under a real determinant-one map. -/
def realSLDisplacementPolynomial (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Polynomial ℂ :=
  C (A 1 0:ℂ)*X^2+C ((A 1 1-A 0 0:ℝ):ℂ)*X-C (A 0 1:ℂ)

theorem realSLDisplacementPolynomial_eval (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    (realSLDisplacementPolynomial A).eval z=
      (A 1 0:ℂ)*z^2+((A 1 1:ℂ)-A 0 0)*z-A 0 1 := by
  simp only [realSLDisplacementPolynomial,eval_sub,eval_add,eval_mul,eval_pow,eval_C,eval_X,Complex.ofReal_sub]

/-- The genuine distance cosh displacement is the norm square of the actual independent quadratic. -/
theorem cosh_realSL_displacement_sub_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    Real.cosh (dist z (A • z))-1=
      ‖(realSLDisplacementPolynomial A).eval (z:ℂ)‖^2/(2*z.im^2) := by
  have htwo:=Real.cosh_two_mul (dist z (A • z)/2)
  rw [show 2*(dist z (A • z)/2)=dist z (A • z) by ring] at htwo
  have hcosh : Real.cosh (dist z (A • z))-1=2*Real.sinh (dist z (A • z)/2)^2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (dist z (A • z)/2)]
  rw [hcosh,hSL_half_displacement_polynomial,realSLDisplacementPolynomial_eval,div_pow]
  field_simp


/-- The genuine squared displacement quadratic is a bivariate polynomial in the actual real and imaginary coordinates. -/
def realSLDisplacementNormBivariate (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Polynomial (Polynomial ℂ) :=
  (((realSLDisplacementPolynomial A).map Polynomial.C).comp Auxiliary.Analysis.complexPlaneVariable)*
    ((((realSLDisplacementPolynomial A).map (starRingEnd ℂ)).map Polynomial.C).comp
      Auxiliary.Analysis.complexPlaneConjugateVariable)

theorem realSLDisplacementNormBivariate_eval (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    Auxiliary.Analysis.complexBivariateEval (realSLDisplacementNormBivariate A) z.im z.re=
      (‖(realSLDisplacementPolynomial A).eval z‖^2:ℂ) := by
  unfold realSLDisplacementNormBivariate
  have hmul (p q : Polynomial (Polynomial ℂ)) :
      Auxiliary.Analysis.complexBivariateEval (p*q) z.im z.re=
        Auxiliary.Analysis.complexBivariateEval p z.im z.re*Auxiliary.Analysis.complexBivariateEval q z.im z.re := by
    simp only [Auxiliary.Analysis.complexBivariateEval,Polynomial.map_mul,Polynomial.eval_mul]
  rw [hmul,Auxiliary.Analysis.complexBivariateEval_lift_comp,Auxiliary.Analysis.complexBivariateEval_lift_comp,
    Auxiliary.Analysis.complexBivariateEval_plane,
    Auxiliary.Analysis.complexBivariateEval_conjugatePlane,
    Auxiliary.Analysis.polynomial_conjugate_eval,
    Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow]

/-- An independent genuine polynomial for the three-center horocycle condition. -/
def realSLHorocycleGramBivariate (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Polynomial (Polynomial ℂ) :=
  4*realSLDisplacementNormBivariate A*realSLDisplacementNormBivariate B-
    (realSLDisplacementNormBivariate A+realSLDisplacementNormBivariate B-
      realSLDisplacementNormBivariate (A⁻¹*B))^2

/-- The polynomial evaluates to the actual metric Gram expression times a strictly positive clearing denominator. -/
theorem realSLHorocycleGramBivariate_eval (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    Auxiliary.Analysis.complexBivariateEval (realSLHorocycleGramBivariate A B) z.im z.re=
      ((4*z.im^4*horocycleMetricGram z (A • z) (B • z):ℝ):ℂ) := by
  let E : Polynomial (Polynomial ℂ)→+*ℂ :=
    (Polynomial.evalRingHom (z.im:ℂ)).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom (z.re:ℂ)))
  have hE (p : Polynomial (Polynomial ℂ)) : Auxiliary.Analysis.complexBivariateEval p z.im z.re=E p:=rfl
  have hnorm (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      E (realSLDisplacementNormBivariate M)=(‖(realSLDisplacementPolynomial M).eval (z:ℂ)‖^2:ℂ) :=
    realSLDisplacementNormBivariate_eval M z
  rw [hE,realSLHorocycleGramBivariate,map_sub,map_mul,map_mul,map_ofNat,map_pow,map_sub,map_add,
    hnorm A,hnorm B,hnorm (A⁻¹*B)]
  have hAB : dist z ((A⁻¹*B) • z)=dist (A • z) (B • z) := by
    rw [mul_smul]
    exact ((isometry_smul ℍ A).dist_eq z (A⁻¹ • B • z)).symm.trans (by rw [smul_inv_smul])
  have hnormReal (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      ‖(realSLDisplacementPolynomial M).eval (z:ℂ)‖^2=
        (2*z.im^2)*(Real.cosh (dist z (M • z))-1) := by
    have hh:=cosh_realSL_displacement_sub_one M z
    exact ((eq_div_iff (by positivity : (2:ℝ)*z.im^2≠0)).mp hh).symm.trans (mul_comm _ _)
  rw [show (‖(realSLDisplacementPolynomial A).eval (z:ℂ)‖:ℂ)^2=
      ((‖(realSLDisplacementPolynomial A).eval (z:ℂ)‖^2:ℝ):ℂ) by norm_cast,
    show (‖(realSLDisplacementPolynomial B).eval (z:ℂ)‖:ℂ)^2=
      ((‖(realSLDisplacementPolynomial B).eval (z:ℂ)‖^2:ℝ):ℂ) by norm_cast,
    show (‖(realSLDisplacementPolynomial (A⁻¹*B)).eval (z:ℂ)‖:ℂ)^2=
      ((‖(realSLDisplacementPolynomial (A⁻¹*B)).eval (z:ℂ)‖^2:ℝ):ℂ) by norm_cast]
  rw [hnormReal A,hnormReal B,hnormReal (A⁻¹*B),hAB]
  unfold horocycleMetricGram
  push_cast
  ring


/-- A nonzero actual bivariate complex polynomial has a genuine zero-area real-coordinate locus. -/
theorem complexBivariate_zero_locus_volume_zero (P : Polynomial (Polynomial ℂ)) (hP : P≠0) :
    volume {z : ℂ | Auxiliary.Analysis.complexBivariateEval P z.im z.re=0}=0 := by
  have hpair:=Auxiliary.Analysis.complexBivariateEval_ae_ne_zero P hP
  have hm : Measure.map Complex.measurableEquivRealProd (volume : Measure ℂ)=
      (volume : Measure ℝ).prod volume:=Complex.volume_preserving_equiv_real_prod.map_eq
  have hmap : ∀ᵐu : ℝ×ℝ ∂Measure.map Complex.measurableEquivRealProd (volume : Measure ℂ),
      Auxiliary.Analysis.complexBivariateEval P u.2 u.1≠0 := by
    rw [hm]
    exact hpair
  have hZ:=MeasureTheory.ae_of_ae_map Complex.measurableEquivRealProd.measurable.aemeasurable hmap
  rw [measure_eq_zero_iff_ae_notMem]
  exact hZ

/-- For a nonzero independently defined Gram polynomial, the actual three-center horocycle degeneration has zero genuine hyperbolic area. -/
theorem realSLHorocycleGram_volume_zero (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hP : realSLHorocycleGramBivariate A B≠0) :
    volume {z : ℍ | horocycleMetricGram z (A • z) (B • z)=0}=0 := by
  have hnull : (volume : Measure ℂ) (((↑):ℍ→ℂ) '' {z : ℍ | horocycleMetricGram z (A • z) (B • z)=0})=0 := by
    apply measure_mono_null _ (complexBivariate_zero_locus_volume_zero _ hP)
    rintro _ ⟨z,hz,rfl⟩
    change Auxiliary.Analysis.complexBivariateEval (realSLHorocycleGramBivariate A B) z.im z.re=0
    rw [realSLHorocycleGramBivariate_eval,hz,mul_zero,Complex.ofReal_zero]
  rw [UpperHalfPlane.volume_eq_lintegral,Measure.restrict_eq_zero.mpr hnull]
  simp

end LowDimensionalTopology.Geometry.Hyperbolic
