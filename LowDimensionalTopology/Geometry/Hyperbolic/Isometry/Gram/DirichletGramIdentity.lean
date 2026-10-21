/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.Polynomial.DirichletGramAlgebra
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Gram.DirichletHorocycleGram
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Polynomial
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Euclidean

/-- Upper-half-plane vanishing of a genuine bivariate polynomial forces the independent polynomial itself to vanish. -/
theorem complexBivariate_eq_zero_of_upperHalfPlane_eval_zero (P : Polynomial (Polynomial ℂ))
    (hP : ∀z : ℍ, Auxiliary.Analysis.complexBivariateEval P z.im z.re=0) : P=0 := by
  have hreal (p : Polynomial ℂ) (hp : ∀x : ℝ,p.eval (x:ℂ)=0) : p=0 := by
    by_contra hn
    have hf:=Auxiliary.Analysis.complex_polynomial_real_roots_finite p hn
    have he : {x : ℝ | p.eval (x:ℂ)=0}=Set.univ := by ext x;simp [hp]
    rw [he] at hf
    exact Set.infinite_univ hf
  have houter (x : ℝ) : P.map (Polynomial.evalRingHom (x:ℂ))=0 := by
    by_contra hn
    have hf:=Auxiliary.Analysis.complex_polynomial_real_roots_finite _ hn
    have hsub : Set.Ioi (0:ℝ) ⊆ {y : ℝ | (P.map (Polynomial.evalRingHom (x:ℂ))).eval (y:ℂ)=0} := by
      intro y hy
      have he:=hP ⟨(x:ℂ)+(y:ℂ)*Complex.I,by simpa using hy⟩
      change Auxiliary.Analysis.complexBivariateEval P ((x:ℂ)+(y:ℂ)*Complex.I).im ((x:ℂ)+(y:ℂ)*Complex.I).re=0 at he
      simpa [Auxiliary.Analysis.complexBivariateEval] using he
    exact Set.Ioi_infinite (0:ℝ) (hf.subset hsub)
  apply Polynomial.ext
  intro n
  apply hreal
  intro x
  have he:=congrArg (fun p : Polynomial ℂ=>p.coeff n) (houter x)
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at he
  exact he

/-- Independent polynomial vanishing is equivalent to the genuine metric identity on every actual point. -/
theorem realSLHorocycleGramBivariate_eq_zero_iff (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    realSLHorocycleGramBivariate A B=0 ↔ ∀z : ℍ,horocycleMetricGram z (A • z) (B • z)=0 := by
  constructor
  · intro h z
    have he:=realSLHorocycleGramBivariate_eval A B z
    rw [h] at he
    simp only [Auxiliary.Analysis.complexBivariateEval,Polynomial.map_zero,Polynomial.eval_zero] at he
    have hr : 4*z.im^4*horocycleMetricGram z (A • z) (B • z)=0 := Complex.ofReal_eq_zero.mp he.symm
    exact (mul_eq_zero.mp hr).resolve_left (by positivity)
  · intro h
    apply complexBivariate_eq_zero_of_upperHalfPlane_eval_zero
    intro z
    rw [realSLHorocycleGramBivariate_eval,h z,mul_zero,Complex.ofReal_zero]

/-- The genuine Gram identity transports under conjugation by an actual determinant-one upper-half-plane isometry. -/
theorem realSLHorocycleGramBivariate_conjugate_eq_zero (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : realSLHorocycleGramBivariate A B=0) :
    realSLHorocycleGramBivariate (q*A*q⁻¹) (q*B*q⁻¹)=0 := by
  apply (realSLHorocycleGramBivariate_eq_zero_iff _ _).mpr
  intro z
  have hh:=(realSLHorocycleGramBivariate_eq_zero_iff A B).mp h (q⁻¹ • z)
  have he:=horocycleMetricGram_realGL_smul (Matrix.SpecialLinearGroup.mapGL ℝ q)
    (q⁻¹ • z) (A • q⁻¹ • z) (B • q⁻¹ • z)
  change horocycleMetricGram (q • q⁻¹ • z) (q • A • q⁻¹ • z) (q • B • q⁻¹ • z)=_ at he
  simpa only [smul_inv_smul,mul_smul] using he.trans hh

/-- The real polynomial numerator is the actual complex displacement norm, evaluated on the real polynomial curve. -/
theorem gramDisplacementNormPolynomial_eval (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (x y : Polynomial ℝ) (t : ℝ) :
    (Auxiliary.Algebra.gramDisplacementNormPolynomial (A 0 0) (A 0 1) (A 1 0) (A 1 1) x y).eval t=
      ‖(realSLDisplacementPolynomial A).eval (((x.eval t:ℝ):ℂ)+((y.eval t:ℝ):ℂ)*Complex.I)‖^2 := by
  rw [realSLDisplacementPolynomial_eval,←Complex.normSq_eq_norm_sq]
  simp [Auxiliary.Algebra.gramDisplacementNormPolynomial,Complex.normSq_apply,Complex.add_re,Complex.mul_re,
    Complex.add_im,Complex.mul_im,pow_two]
  ring



/-- Evaluation of the independent complex Gram polynomial agrees with the explicit real polynomial numerator on every real polynomial curve, including boundary points. -/
theorem gramPairPolynomial_eval_complex (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (x y : Polynomial ℝ) (t : ℝ) :
    Auxiliary.Analysis.complexBivariateEval (realSLHorocycleGramBivariate A B) (y.eval t) (x.eval t)=
      (((Auxiliary.Algebra.gramPairPolynomial (A 0 0) (A 0 1) (A 1 0) (A 1 1)
        (B 0 0) (B 0 1) (B 1 0) (B 1 1) x y).eval t:ℝ):ℂ) := by
  let z:ℂ:=((x.eval t:ℝ):ℂ)+((y.eval t:ℝ):ℂ)*Complex.I
  have hre : z.re=x.eval t:=by simp [z]
  have him : z.im=y.eval t:=by simp [z]
  let E : Polynomial (Polynomial ℂ)→+*ℂ :=
    (Polynomial.evalRingHom ((y.eval t:ℝ):ℂ)).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom ((x.eval t:ℝ):ℂ)))
  change E (realSLHorocycleGramBivariate A B)=_
  have hnorm (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      E (realSLDisplacementNormBivariate M)=
        (((Auxiliary.Algebra.gramDisplacementNormPolynomial (M 0 0) (M 0 1) (M 1 0) (M 1 1) x y).eval t:ℝ):ℂ) := by
    have he:=realSLDisplacementNormBivariate_eval M z
    rw [hre,him] at he
    change E (realSLDisplacementNormBivariate M)=_ at he
    rw [he,gramDisplacementNormPolynomial_eval]
    simp only [Complex.ofReal_pow,z]
  rw [realSLHorocycleGramBivariate,map_sub,map_mul,map_mul,map_ofNat,map_pow,map_sub,map_add,
    hnorm A,hnorm B,hnorm (A⁻¹*B)]
  have h00 : (A⁻¹*B) 0 0=A 1 1*B 0 0-A 0 1*B 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,Matrix.mul_apply,
      Matrix.adjugate_fin_two,Fin.sum_univ_two,sub_eq_add_neg]
  have h01 : (A⁻¹*B) 0 1=A 1 1*B 0 1-A 0 1*B 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,Matrix.mul_apply,
      Matrix.adjugate_fin_two,Fin.sum_univ_two,sub_eq_add_neg]
  have h10 : (A⁻¹*B) 1 0=A 0 0*B 1 0-A 1 0*B 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,Matrix.mul_apply,
      Matrix.adjugate_fin_two,Fin.sum_univ_two,sub_eq_add_neg,add_comm]
  have h11 : (A⁻¹*B) 1 1=A 0 0*B 1 1-A 1 0*B 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,Matrix.mul_apply,
      Matrix.adjugate_fin_two,Fin.sum_univ_two,sub_eq_add_neg,add_comm]
  rw [h00,h01,h10,h11]
  simp only [Auxiliary.Algebra.gramPairPolynomial,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Complex.ofReal_sub,Complex.ofReal_add,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]

/-- True independent polynomial degeneracy supplies every real polynomial-curve identity needed by the normal-form classifications. -/
theorem realSLHorocycleGram_zero_curve_identity (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : realSLHorocycleGramBivariate A B=0) (x y : Polynomial ℝ) :
    Auxiliary.Algebra.gramPairPolynomial (A 0 0) (A 0 1) (A 1 0) (A 1 1)
      (B 0 0) (B 0 1) (B 1 0) (B 1 1) x y=0 := by
  apply Polynomial.zero_of_eval_zero
  intro t
  have he:=gramPairPolynomial_eval_complex A B x y t
  rw [h] at he
  simp only [Auxiliary.Analysis.complexBivariateEval,Polynomial.map_zero,Polynomial.eval_zero] at he
  exact Complex.ofReal_eq_zero.mp he.symm



/-- In a genuine elliptic normal form an identically vanishing three-center Gram polynomial leaves only the identity or the first actual transformation. -/
theorem realSLHorocycleGram_rotation_zero_projection (u v : ℝ) (hu : u^2+v^2=1) (hv : v≠0)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : realSLHorocycleGramBivariate (hRotationSL u v hu) B=0) :
    realSLMobius B=1 ∨ realSLMobius B=realSLMobius (hRotationSL u v hu) := by
  have hdet : B 0 0*B 1 1-B 0 1*B 1 0=1 := by
    have hd:=B.det_coe
    rw [Matrix.det_fin_two] at hd
    exact hd
  have hline (dx dy : ℝ) :
      Auxiliary.Algebra.gramPairPolynomial u v (-v) u (B 0 0) (B 0 1) (B 1 0) (B 1 1) (C dx*X) (1+C dy*X)=0 := by
    simpa [hRotationSL] using realSLHorocycleGram_zero_curve_identity _ _ h (C dx*X) (1+C dy*X)
  obtain ⟨had,hcb,hcases⟩:=Auxiliary.Algebra.gramPair_rotation_zero_classification u v _ _ _ _ hu hv hdet hline
  rcases hcases with ⟨hb,ha⟩|⟨k,hk,ha,hb⟩
  · have h0 : B 1 0=0 := by simpa [hb] using hcb
    have ha': (B 0 0)^2=(1:ℝ)^2 := by simpa using ha
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha' with ha1|ha1
    · have he : B=1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [hb,h0,ha1,←had]
      exact Or.inl (by rw [he,map_one])
    · have he : B= -1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg,hb,h0,ha1,←had]
      exact Or.inl (by rw [he,realSLMobius_neg,map_one])
  · have hk' : k^2=(1:ℝ)^2 := by simpa using hk
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hk' with hk1|hk1
    · have he : B=hRotationSL u v hu := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [hRotationSL,hb,hcb,ha,←had,hk1]
      exact Or.inr (congrArg realSLMobius he)
    · have he : B= -hRotationSL u v hu := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [hRotationSL,Matrix.SpecialLinearGroup.coe_neg,hb,hcb,ha,←had,hk1]
      exact Or.inr (by rw [he,realSLMobius_neg])



/-- Independently defined Gram degeneracy depends only on the actual upper-half-plane actions. -/
theorem realSLHorocycleGramBivariate_congr_actions (A B A' B' : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀z : ℍ,A • z=A' • z) (hB : ∀z : ℍ,B • z=B' • z)
    (h : realSLHorocycleGramBivariate A B=0) : realSLHorocycleGramBivariate A' B'=0 := by
  apply (realSLHorocycleGramBivariate_eq_zero_iff _ _).mpr
  intro z
  rw [←hA z,←hB z]
  exact (realSLHorocycleGramBivariate_eq_zero_iff A B).mp h z

/-- For the genuine positive dilation normal form there are no additional projective Gram degeneracies. -/
theorem realSLHorocycleGram_dilation_zero_projection (k : ℝ) (hk : 0<k) (hk1 : k≠1)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : realSLHorocycleGramBivariate (verticalDilationSL k hk) B=0) :
    realSLMobius B=1 ∨ realSLMobius B=realSLMobius (verticalDilationSL k hk) := by
  let t:=Real.sqrt k
  have ht : t≠0:=(Real.sqrt_pos.mpr hk).ne'
  have htsq : t^2=k:=Real.sq_sqrt hk.le
  have hdet : B 0 0*B 1 1-B 0 1*B 1 0=1 := by
    have hd:=B.det_coe
    rw [Matrix.det_fin_two] at hd
    exact hd
  have hY : Auxiliary.Algebra.gramPairPolynomial t 0 0 (1/t) (B 0 0) (B 0 1) (B 1 0) (B 1 1) 0 X=0 := by
    simpa [verticalDilationSL,t] using realSLHorocycleGram_zero_curve_identity _ _ h 0 X
  obtain ⟨hb, hc, hcases⟩:=
    Auxiliary.Algebra.gramPair_diagonal_zero_classification t _ _ _ _ ht (by simpa [htsq] using hk1) hdet hY
  have hd : B 1 1=1/(B 0 0) := by
    rw [hb,hc,mul_zero,sub_zero] at hdet
    exact (eq_div_iff (left_ne_zero_of_mul_eq_one hdet)).mpr (by nlinarith only [hdet])
  rcases hcases with ha|ha
  · have ha': (B 0 0)^2=(1:ℝ)^2:=by simpa using ha
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha' with ha1|ha1
    · have he : B=1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [hb,hc,hd,ha1]
      exact Or.inl (by rw [he,map_one])
    · have he : B= -1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg,hb,hc,hd,ha1]
      exact Or.inl (by rw [he,realSLMobius_neg,map_one])
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with ha1|ha1
    · have he : B=verticalDilationSL k hk := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [verticalDilationSL,hb,hc,hd,ha1,t]
      exact Or.inr (congrArg realSLMobius he)
    · have he : B= -verticalDilationSL k hk := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [verticalDilationSL,Matrix.SpecialLinearGroup.coe_neg,hb,hc,hd,ha1,t]
      exact Or.inr (by rw [he,realSLMobius_neg])



/-- Simultaneous conjugation does not merge distinct original actual transformations. -/
theorem realSLMobius_conjugate_ne (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hne : realSLMobius A≠realSLMobius B) :
    realSLMobius (q*A*q⁻¹)≠realSLMobius (q*B*q⁻¹) := by
  intro he
  apply hne
  simp only [map_mul,map_inv] at he
  exact mul_left_cancel (mul_right_cancel he)

/-- Actual nonidentity is unchanged by genuine simultaneous conjugation. -/
theorem realSLMobius_conjugate_ne_one (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hne : realSLMobius A≠1) : realSLMobius (q*A*q⁻¹)≠1 := by
  intro he
  apply hne
  have hh:=congrArg (fun f : Mobius.complexMobiusGroup=>(realSLMobius q)⁻¹*f*realSLMobius q) he
  simpa only [map_mul,map_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,one_mul,inv_mul_cancel,mul_one] using hh

/-- For two distinct nonidentity actual transformations, identical Gram degeneracy forces the first transformation to be genuinely parabolic. -/
theorem realSLHorocycleGram_zero_forces_parabolic (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1) (hne : realSLMobius A≠realSLMobius B)
    (h : realSLHorocycleGramBivariate A B=0) : Mobius.MobiusParabolic (realSLMobius A) := by
  rcases lt_trichotomy ((Matrix.trace A.val)^2) 4 with hlt|heq|hgt
  · have heA:Mobius.MobiusElliptic (realSLMobius A):=(realSLMobius_elliptic_iff A hA).mpr hlt
    obtain ⟨q,u,v,hu,_hcenter,hv,hrot⟩:=realSLMobius_elliptic_normal_form A heA
    have hQ:=realSLHorocycleGramBivariate_conjugate_eq_zero A B q h
    rw [hrot] at hQ
    rcases realSLHorocycleGram_rotation_zero_projection u v hu hv (q*B*q⁻¹) hQ with h1|h1
    · exact False.elim (realSLMobius_conjugate_ne_one B q hB h1)
    · rw [←hrot] at h1
      exact False.elim (realSLMobius_conjugate_ne A B q hne h1.symm)
  · exact (realSLMobius_parabolic_iff A hA).mpr heq
  · obtain ⟨q,k,hk,hk1,_hproj,hact⟩:=realSLMobius_hyperbolic_normalizer A hA hgt
    have hQ:=realSLHorocycleGramBivariate_conjugate_eq_zero A B q h
    have hQ':realSLHorocycleGramBivariate (verticalDilationSL k hk) (q*B*q⁻¹)=0 :=
      realSLHorocycleGramBivariate_congr_actions _ _ _ _ hact (fun _=>rfl) hQ
    rcases realSLHorocycleGram_dilation_zero_projection k hk hk1 (q*B*q⁻¹) hQ' with h1|h1
    · exact False.elim (realSLMobius_conjugate_ne_one B q hB h1)
    · have hp:=realSLMobius_ext_action (q*A*q⁻¹) (verticalDilationSL k hk) hact
      rw [←hp] at h1
      exact False.elim (realSLMobius_conjugate_ne A B q hne h1.symm)

/-- In a genuine nonzero translation normal form, identical Gram degeneracy forces the second actual map to fix infinity. -/
theorem realSLHorocycleGram_translation_zero_fixed_infty (t : ℝ) (ht : t≠0)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : realSLHorocycleGramBivariate (hTranslationSL t) B=0) :
    (realSLMobius B).val ∞=∞ := by
  have hdet : B 0 0*B 1 1-B 0 1*B 1 0=1 := by
    have hd:=B.det_coe
    rw [Matrix.det_fin_two] at hd
    exact hd
  have hX : Auxiliary.Algebra.gramPairPolynomial 1 t 0 1 (B 0 0) (B 0 1) (B 1 0) (B 1 1) X 0=0 := by
    simpa [hTranslationSL] using realSLHorocycleGram_zero_curve_identity _ _ h X 0
  have hY : Auxiliary.Algebra.gramPairPolynomial 1 t 0 1 (B 0 0) (B 0 1) (B 1 0) (B 1 1) 0 X=0 := by
    simpa [hTranslationSL] using realSLHorocycleGram_zero_curve_identity _ _ h 0 X
  obtain ⟨hc,_⟩:=Auxiliary.Algebra.gramPair_translation_zero_forces_common_infty t _ _ _ _ ht hdet hX hY
  exact (realSLMobius_fixed_infty_iff B).mpr hc



/-- Genuine parabolic Gram degeneracy forces the second actual transformation to fix the same actual ideal point. -/
theorem realSLHorocycleGram_parabolic_zero_common_fixed (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) (h : realSLHorocycleGramBivariate A B=0) :
    ∃ξ : Mobius.ExtendedComplex, ξ∈halfPlaneIdealBoundary ∧
      (realSLMobius A).val ξ=ξ ∧ (realSLMobius B).val ξ=ξ := by
  obtain ⟨q,t,ht,hnorm⟩:=realSLMobius_parabolic_normal_form A hA
  have hQ:=realSLHorocycleGramBivariate_conjugate_eq_zero A B q h
  have hT : realSLHorocycleGramBivariate (hTranslationSL t) (q*B*q⁻¹)=0 := by
    rcases hnorm with hn|hn
    · simpa only [hn] using hQ
    · rw [hn] at hQ
      exact realSLHorocycleGramBivariate_congr_actions _ _ _ _
        (by
          intro z
          apply UpperHalfPlane.ext
          apply OnePoint.coe_injective
          rw [←realSLMobius_action,←realSLMobius_action,realSLMobius_neg]) (fun _=>rfl) hQ
  have hBfix:=realSLHorocycleGram_translation_zero_fixed_infty t ht (q*B*q⁻¹) hT
  have hAfix : (realSLMobius (q*A*q⁻¹)).val ∞=∞ := by
    apply (realSLMobius_fixed_infty_iff _).mpr
    rcases hnorm with hn|hn
    · rw [hn];simp [hTranslationSL]
    · rw [hn];simp [hTranslationSL,Matrix.SpecialLinearGroup.coe_neg]
  let ξ : Mobius.ExtendedComplex:=(realSLMobius q).val.symm ∞
  have hAξ : (realSLMobius A).val ξ=ξ := by
    apply (realSLMobius_conjugate_fixed_iff A q ξ).mp
    simpa only [ξ,Equiv.apply_symm_apply] using hAfix
  have hBξ : (realSLMobius B).val ξ=ξ := by
    apply (realSLMobius_conjugate_fixed_iff B q ξ).mp
    simpa only [ξ,Equiv.apply_symm_apply] using hBfix
  exact ⟨ξ,realSLMobius_parabolic_fixed_boundary A hA ξ hAξ,hAξ,hBξ⟩

/-- The complete genuine projective identity classification for distinct nonidentity transformations: they are parabolic with one common actual ideal fixed point. -/
theorem realSLHorocycleGram_zero_classification (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1) (hne : realSLMobius A≠realSLMobius B)
    (h : realSLHorocycleGramBivariate A B=0) :
    Mobius.MobiusParabolic (realSLMobius A) ∧ Mobius.MobiusParabolic (realSLMobius B) ∧
      ∃ξ : Mobius.ExtendedComplex, ξ∈halfPlaneIdealBoundary ∧
        (realSLMobius A).val ξ=ξ ∧ (realSLMobius B).val ξ=ξ := by
  have hAp:=realSLHorocycleGram_zero_forces_parabolic A B hA hB hne h
  have hswap : realSLHorocycleGramBivariate B A=0 := by
    apply (realSLHorocycleGramBivariate_eq_zero_iff _ _).mpr
    intro z
    have hz:=(realSLHorocycleGramBivariate_eq_zero_iff A B).mp h z
    unfold horocycleMetricGram at hz ⊢
    rw [dist_comm (B • z) (A • z)]
    convert hz using 1; ring
  exact ⟨hAp,realSLHorocycleGram_zero_forces_parabolic B A hB hA hne.symm hswap,
    realSLHorocycleGram_parabolic_zero_common_fixed A B hAp h⟩

end LowDimensionalTopology.Geometry.Hyperbolic
