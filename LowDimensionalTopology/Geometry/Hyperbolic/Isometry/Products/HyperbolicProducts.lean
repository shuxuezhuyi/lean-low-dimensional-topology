/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicHalfTurns
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.AngleMeasures
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalReconstruction
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

/-- A fixed real ideal point satisfies the exact original real fractional quadratic. -/
theorem hSL_fixed_real_polynomial (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : ℝ)
    (hx : (realSLMobius A).val ((x:ℂ):Mobius.ExtendedComplex)=((x:ℂ):Mobius.ExtendedComplex)) :
    A 1 0*x^2+(A 1 1-A 0 0)*x-A 0 1=0 := by
  have h := (Mobius.Classification.fractionalLinear_fixed_coe_iff
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom A)) (x:ℂ)).mp
      (show Mobius.fractionalLinear _ ((x:ℂ):Mobius.ExtendedComplex)=((x:ℂ):Mobius.ExtendedComplex) by
        simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action] using hx)
  change (A 1 0:ℂ)*((x:ℂ)*(x:ℂ))+((A 1 1:ℂ)-A 0 0)*(x:ℂ)+ -(A 0 1:ℂ)=0 at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_re,pow_two,sub_eq_add_neg] using hr

/-- The signed scalar of the actual axis reflection in the centered real matrix. -/
def hAxisReflectionCoefficient (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : HalfPlaneLine → ℝ
  | .vertical _ => (A 1 1-A 0 0)/2
  | .circle _ _ _ => A 1 0

/-- A real matrix fixing both actual ideal ends of a line has the exact centered reflection decomposition. -/
theorem hSL_axis_reflection_decomposition (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L : HalfPlaneLine) (hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p) :
    A.val=(Matrix.trace A.val/2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)+
      hAxisReflectionCoefficient A L • L.reflectionMatrix.val := by
  cases L with
  | vertical x =>
    have hi : (realSLMobius A).val ∞=∞ := hL ∞ (by rw [vertical_idealEndpoints];simp)
    have hx : (realSLMobius A).val ((x:ℂ):Mobius.ExtendedComplex)=((x:ℂ):Mobius.ExtendedComplex) :=
      hL _ (by rw [vertical_idealEndpoints];simp)
    have hc := (realSLMobius_fixed_infty_iff A).mp hi
    have hb := hSL_fixed_real_polynomial A x hx
    rw [hc,zero_mul,zero_add] at hb
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [hAxisReflectionCoefficient,HalfPlaneLine.reflectionMatrix,
      verticalReflectionMatrix,Matrix.trace_fin_two]
    all_goals nlinarith
  | circle c r hr =>
    have hplus := hSL_fixed_real_polynomial A (c+r) (hL _ (by rw [circle_idealEndpoints];simp))
    have hminus := hSL_fixed_real_polynomial A (c-r) (hL _ (by rw [circle_idealEndpoints];simp))
    have hp : r*(A 1 1-A 0 0+2*c*A 1 0)=0 := by nlinarith
    have hd := (mul_eq_zero.mp hp).resolve_left hr.ne'
    have hb : A 0 1=A 1 0*(r^2-c^2) := by nlinarith
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [hAxisReflectionCoefficient,HalfPlaneLine.reflectionMatrix,
      circleReflectionMatrix,Matrix.trace_fin_two]
    all_goals nlinarith

/-- The signed hyperbolic parameter couples the original lift to its actual axis normal. -/
def hAxisSignedSine (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L : HalfPlaneLine) : ℝ :=
  hAxisReflectionCoefficient A L*L.reflectionScale

/-- The exact determinant-one identity for the actual axis decomposition. -/
theorem hSL_axis_signedSine_sq (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L : HalfPlaneLine)
    (hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p) :
    hAxisSignedSine A L^2=(Matrix.trace A.val/2)^2-1 := by
  have hd:=A.det_coe
  rw [hSL_axis_reflection_decomposition A L hL] at hd
  cases L
  all_goals simp [Matrix.det_fin_two,hAxisSignedSine,hAxisReflectionCoefficient,
    HalfPlaneLine.reflectionScale,HalfPlaneLine.reflectionMatrix,
    verticalReflectionMatrix,circleReflectionMatrix] at hd ⊢
  all_goals nlinarith

/-- The trace of centered two-by-two factors retains exactly their bilinear cross term. -/
theorem hMatrix_trace_centered_product (R S : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : Matrix.trace R=0) (hS : Matrix.trace S=0) (a b c d : ℝ) :
    Matrix.trace ((a • (1 : Matrix (Fin 2) (Fin 2) ℝ)+c • R)*
      (b • (1 : Matrix (Fin 2) (Fin 2) ℝ)+d • S))/2=
        a*b+c*d*Matrix.trace (R*S)/2 := by
  rw [Matrix.trace_fin_two] at hR hS
  simp only [Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.add_apply,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  norm_num
  linear_combination (a*d/2)*hS+(b*c/2)*hR

/-- The literal reflection-matrix pairing equals the true signed Lorentz side pairing. -/
theorem hReflectionMatrix_trace_pairing (L M : HalfPlaneLine) :
    Matrix.trace (L.reflectionMatrix.val*M.reflectionMatrix.val)/2=
      (L.reflectionScale*M.reflectionScale)*
        (inner ℝ L.incenterNormal M.incenterNormal-L.incenterOffset*M.incenterOffset) := by
  have h:=reflectionProductSL_trace_pairing L M
  rw [reflectionProductSL_coe,Matrix.trace_smul,smul_eq_mul] at h
  have hL:=L.reflectionScale_pos.ne'
  have hM:=M.reflectionScale_pos.ne'
  field_simp [hL,hM] at h
  nlinarith

/-- Exact signed trace identity for two original real transformations fixing their actual axis ends. -/
theorem hSL_product_trace_axis_pairing
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine)
    (hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p)
    (hM : ∀p∈M.idealEndpoints,(realSLMobius B).val p=p) :
    Matrix.trace (A*B).val/2=(Matrix.trace A.val/2)*(Matrix.trace B.val/2)+
      hAxisSignedSine A L*hAxisSignedSine B M*
        (inner ℝ L.incenterNormal M.incenterNormal-L.incenterOffset*M.incenterOffset) := by
  change Matrix.trace (A.val*B.val)/2= _
  conv_lhs => rw [hSL_axis_reflection_decomposition A L hL,hSL_axis_reflection_decomposition B M hM]
  rw [hMatrix_trace_centered_product _ _ L.reflectionMatrix_trace M.reflectionMatrix_trace,
    show hAxisReflectionCoefficient A L*hAxisReflectionCoefficient B M*
      Matrix.trace (L.reflectionMatrix.val*M.reflectionMatrix.val)/2=
      (hAxisReflectionCoefficient A L*hAxisReflectionCoefficient B M)*
      (Matrix.trace (L.reflectionMatrix.val*M.reflectionMatrix.val)/2) by ring,
    hReflectionMatrix_trace_pairing]
  dsimp only [hAxisSignedSine]
  ring

/-- The actual axis coefficient has precisely the hyperbolic sine of half the true translation length. -/
theorem hAxisSignedSine_abs_eq_sinh_translation
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : realSLMobius A≠1)
    (ht : 4 < (Matrix.trace A.val)^2) :
    |hAxisSignedSine A (hHyperbolicAxis A hf ht)|=
      Real.sinh (hTranslationLength (hSLIsometry A)/2) := by
  have hends : ∀p∈(hHyperbolicAxis A hf ht).idealEndpoints,(realSLMobius A).val p=p := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hsq:=hSL_axis_signedSine_sq A _ hends
  have htr:=hHyperbolic_translation_abs_trace A hf ht
  have hT : 0 < hTranslationLength (hSLIsometry A)/2 := by
    have h:=hHyperbolic_translationLength_pos A hf ht
    linarith
  apply (sq_eq_sq₀ (abs_nonneg _) (Real.sinh_pos_iff.mpr hT).le).mp
  rw [sq_abs,hsq]
  have hs:=Real.cosh_sq_sub_sinh_sq (hTranslationLength (hSLIsometry A)/2)
  have hc:=congrArg (fun t : ℝ=>t^2) htr
  rw [div_pow,sq_abs] at hc
  nlinarith

/-- The signed side pairing of the two actual axis normals and offsets. -/
def hAxisPairing (L M : HalfPlaneLine) : ℝ :=
  inner ℝ L.incenterNormal M.incenterNormal-L.incenterOffset*M.incenterOffset

/-- The absolute value of a real sum is recovered from the two magnitudes and their relative sign. -/
theorem abs_add_eq_signed_abs (x y : ℝ) :
    |x+y|=|(|x|)+(if 0≤x*y then (1:ℝ) else -1)*(|y|)| := by
  by_cases hxy : 0≤x*y
  · rw [ite_eq_left hxy,one_mul]
    have h : |x| * |y|=x*y := by rw [←abs_mul,abs_of_nonneg hxy]
    apply (sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs,sq_abs]
    nlinarith [sq_abs x,sq_abs y]
  · rw [ite_eq_right hxy,neg_one_mul]
    have h : |x| * |y|= -(x*y) := by rw [←abs_mul,abs_of_neg (lt_of_not_ge hxy)]
    apply (sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs,sq_abs]
    nlinarith [sq_abs x,sq_abs y]

/-- A lift-independent relative sign computed from the two actual transformations and their actual axis normals. -/
def hRelativeAxisSign (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine) : ℝ :=
  if 0≤((Matrix.trace A.val/2)*(Matrix.trace B.val/2))*
    (hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M) then 1 else -1

theorem hRelativeAxisSign_eq_one_or_neg_one
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine) :
    hRelativeAxisSign A B L M=1 ∨ hRelativeAxisSign A B L M= -1 := by
  unfold hRelativeAxisSign
  split_ifs <;> simp

/-- The genuine hyperbolic product trace has the exact two-axis signed-pairing expression. -/
theorem hHyperbolic_product_abs_trace_axis_pairing
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2) :
    let L:=hHyperbolicAxis A hA htA
    let M:=hHyperbolicAxis B hB htB
    |Matrix.trace (A*B).val|/2=
      |Real.cosh (hTranslationLength (hSLIsometry A)/2)*Real.cosh (hTranslationLength (hSLIsometry B)/2)+
        hRelativeAxisSign A B L M*Real.sinh (hTranslationLength (hSLIsometry A)/2)*
          Real.sinh (hTranslationLength (hSLIsometry B)/2)*(|hAxisPairing L M|)| := by
  let L:=hHyperbolicAxis A hA htA
  let M:=hHyperbolicAxis B hB htB
  have hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hM : ∀p∈M.idealEndpoints,(realSLMobius B).val p=p := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hp:=hSL_product_trace_axis_pairing A B L M hL hM
  change Matrix.trace (A*B).val/2=(Matrix.trace A.val/2)*(Matrix.trace B.val/2)+
    hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M at hp
  have h:=congrArg abs hp
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_add_eq_signed_abs,
    abs_mul,abs_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),
    hHyperbolic_translation_abs_trace A hA htA,hHyperbolic_translation_abs_trace B hB htB] at h
  rw [abs_mul,abs_mul,hAxisSignedSine_abs_eq_sinh_translation A hA htA,
    hAxisSignedSine_abs_eq_sinh_translation B hB htB] at h
  change _=|_+hRelativeAxisSign A B L M*(_*_*_)| at h
  simpa only [L,M,mul_assoc] using h

/-- 's exact trace identity for genuinely disjoint actual axes, with an explicit relative sign. -/
theorem hHyperbolic_product_abs_trace_disjoint
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hdis : (hHyperbolicAxis A hA htA).HDisjoint (hHyperbolicAxis B hB htB)) :
    let L:=hHyperbolicAxis A hA htA
    let M:=hHyperbolicAxis B hB htB
    |Matrix.trace (A*B).val|/2=
      |hRelativeAxisSign A B L M*Real.cosh (L.lineDist M)*
        Real.sinh (hTranslationLength (hSLIsometry A)/2)*Real.sinh (hTranslationLength (hSLIsometry B)/2)+
        Real.cosh (hTranslationLength (hSLIsometry A)/2)*Real.cosh (hTranslationLength (hSLIsometry B)/2)| := by
  have h:=hHyperbolic_product_abs_trace_axis_pairing A B hA hB htA htB
  have hp:=halfPlane_inversiveProduct_eq_cosh_lineDist _ _ hdis
  rw [halfPlane_inversiveProduct_eq_normal_product] at hp
  change |hAxisPairing _ _|= _ at hp
  dsimp only at h ⊢
  rw [hp] at h
  rw [h]
  congr 1
  ring

/-- Reversing a real lift negates its signed axis coefficient. -/
theorem hAxisSignedSine_neg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L : HalfPlaneLine) :
    hAxisSignedSine (-A) L= -hAxisSignedSine A L := by
  cases L
  all_goals simp [hAxisSignedSine,hAxisReflectionCoefficient,Matrix.SpecialLinearGroup.coe_neg]
  all_goals ring

/-- The relative sign is unchanged by either representative sign. -/
theorem hRelativeAxisSign_neg_left (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine) :
    hRelativeAxisSign (-A) B L M=hRelativeAxisSign A B L M := by
  unfold hRelativeAxisSign
  rw [hAxisSignedSine_neg,Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_neg]
  congr 2
  ring

theorem hRelativeAxisSign_neg_right (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine) :
    hRelativeAxisSign A (-B) L M=hRelativeAxisSign A B L M := by
  unfold hRelativeAxisSign
  rw [hAxisSignedSine_neg,Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_neg]
  congr 2
  ring

/-- Thus the sign depends on the genuine sphere transformations, independently of both SL lifts. -/
theorem hRelativeAxisSign_congr (A B A' B' : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L M : HalfPlaneLine) (hA : realSLMobius A=realSLMobius A')
    (hB : realSLMobius B=realSLMobius B') : hRelativeAxisSign A B L M=hRelativeAxisSign A' B' L M := by
  rcases (realSLMobius_eq_iff_sign A A').mp hA with heA | heA
  · rw [heA]
    rcases (realSLMobius_eq_iff_sign B B').mp hB with heB | heB
    · rw [heB]
    · rw [heB,hRelativeAxisSign_neg_right]
  · rw [heA,hRelativeAxisSign_neg_left]
    rcases (realSLMobius_eq_iff_sign B B').mp hB with heB | heB
    · rw [heB]
    · rw [heB,hRelativeAxisSign_neg_right]


/-- Inverting the genuine transformation reverses its signed axis parameter. -/
theorem hAxisSignedSine_inv (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L : HalfPlaneLine) :
    hAxisSignedSine A⁻¹ L= -hAxisSignedSine A L := by
  cases L
  all_goals simp [hAxisSignedSine,hAxisReflectionCoefficient,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  all_goals ring

/-- The identity transformation has squared lift trace four, including the negative lift. -/
theorem hSL_trace_sq_of_projection_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A=1) : (Matrix.trace A.val)^2=4 := by
  have he : realSLMobius A=realSLMobius 1 := by simpa using hA
  rcases (realSLMobius_eq_iff_sign A 1).mp he with he | he
  · rw [←he]
    norm_num [Matrix.trace_fin_two]
  · have h : A= -1 := by simpa using (congrArg Neg.neg he).symm
    rw [h]
    norm_num [Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_fin_two]

/-- The nonelliptic trace bound remains valid when the transformation is the identity. -/
theorem hSL_not_elliptic_abs_trace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ¬Mobius.MobiusElliptic (realSLMobius A)) : 2≤|Matrix.trace A.val| := by
  by_cases hi : realSLMobius A=1
  · have hs:=hSL_trace_sq_of_projection_one A hi
    nlinarith [sq_abs (Matrix.trace A.val),abs_nonneg (Matrix.trace A.val)]
  · have hs : 4≤(Matrix.trace A.val)^2 := le_of_not_gt (fun h=>(hA ((realSLMobius_elliptic_iff A hi).mpr h)))
    nlinarith [sq_abs (Matrix.trace A.val),abs_nonneg (Matrix.trace A.val)]

/-- Two nonelliptic signed sums force separation of their real magnitudes. -/
theorem abs_magnitudes_sub_lower_bound (x y : ℝ)
    (hp : 1≤|x+y|) (hm : 1≤|x-y|) : 1≤|(|x|)-(|y|)| := by
  by_cases hx : 0≤x
  · by_cases hy : 0≤y
    · simpa only [abs_of_nonneg hx,abs_of_nonneg hy] using hm
    · simpa only [abs_of_nonneg hx,abs_of_neg (lt_of_not_ge hy),sub_neg_eq_add] using hp
  · by_cases hy : 0≤y
    · rw [abs_of_neg (lt_of_not_ge hx),abs_of_nonneg hy,
        show -x-y= -(x+y) by ring,abs_neg]
      exact hp
    · rw [abs_of_neg (lt_of_not_ge hx),abs_of_neg (lt_of_not_ge hy),
        show -x- -y= -(x-y) by ring,abs_neg]
      exact hm

/-- The inverse-product trace uses the same true axis and the opposite signed cross term. -/
theorem hSL_inverse_product_trace_axis_pairing
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine)
    (hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p)
    (hM : ∀p∈M.idealEndpoints,(realSLMobius B).val p=p) :
    Matrix.trace (A*B⁻¹).val/2=(Matrix.trace A.val/2)*(Matrix.trace B.val/2)-
      hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M := by
  have hMi : ∀p∈M.idealEndpoints,(realSLMobius B⁻¹).val p=p := by
    intro p hp
    simpa only [map_inv] using Mobius.mobius_inv_fixed (hM p hp)
  rw [hSL_product_trace_axis_pairing A B⁻¹ L M hL hMi,hSL_trace_inverse,hAxisSignedSine_inv]
  dsimp only [hAxisPairing]
  ring

/--
For actual hyperbolic axes and their actual translation lengths.
The two nonelliptic products may include the identity.
-/
theorem hHyperbolic_equal_translation_disjoint_bound
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hT : hTranslationLength (hSLIsometry A)=hTranslationLength (hSLIsometry B))
    (hdis : (hHyperbolicAxis A hA htA).HDisjoint (hHyperbolicAxis B hB htB))
    (hp : ¬Mobius.MobiusElliptic (realSLMobius (A*B)))
    (hm : ¬Mobius.MobiusElliptic (realSLMobius (A*B⁻¹))) :
    1≤Real.sinh ((hHyperbolicAxis A hA htA).lineDist (hHyperbolicAxis B hB htB)/2)*
      Real.sinh (hTranslationLength (hSLIsometry A)/2) := by
  let L:=hHyperbolicAxis A hA htA
  let M:=hHyperbolicAxis B hB htB
  let T:=hTranslationLength (hSLIsometry A)/2
  let d:=L.lineDist M
  have hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hM : ∀p∈M.idealEndpoints,(realSLMobius B).val p=p := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  let x:=(Matrix.trace A.val/2)*(Matrix.trace B.val/2)
  let y:=hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M
  have hplus : 1≤|x+y| := by
    have he:=hSL_product_trace_axis_pairing A B L M hL hM
    change Matrix.trace (A*B).val/2=x+y at he
    rw [←he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have h:=hSL_not_elliptic_abs_trace (A*B) hp
    linarith
  have hminus : 1≤|x-y| := by
    have he:=hSL_inverse_product_trace_axis_pairing A B L M hL hM
    change Matrix.trace (A*B⁻¹).val/2=x-y at he
    rw [←he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have h:=hSL_not_elliptic_abs_trace (A*B⁻¹) hm
    linarith
  have hx : |x|=Real.cosh T^2 := by
    dsimp only [x]
    rw [abs_mul,abs_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),
      hHyperbolic_translation_abs_trace A hA htA,hHyperbolic_translation_abs_trace B hB htB,←hT]
    simp only [T,pow_two]
  have hy : |y|=Real.sinh T^2*Real.cosh d := by
    have he:=halfPlane_inversiveProduct_eq_cosh_lineDist L M hdis
    rw [halfPlane_inversiveProduct_eq_normal_product] at he
    change |hAxisPairing L M|=Real.cosh d at he
    dsimp only [y]
    rw [abs_mul,abs_mul,hAxisSignedSine_abs_eq_sinh_translation A hA htA,
      hAxisSignedSine_abs_eq_sinh_translation B hB htB,←hT,he]
    simp only [T,pow_two]
  have hgap:=abs_magnitudes_sub_lower_bound x y hplus hminus
  rw [hx,hy] at hgap
  have hTp : 0<T := by
    have h:=hHyperbolic_translationLength_pos A hA htA
    dsimp only [T]
    linarith
  have hdp : 0<d := L.lineDist_pos M hdis
  have hsp : 0<Real.sinh T := Real.sinh_pos_iff.mpr hTp
  have hdp' : 0<d/2 := by linarith
  have hsd : 0<Real.sinh (d/2) := Real.sinh_pos_iff.mpr hdp'
  have hid:=Real.cosh_sq_sub_sinh_sq T
  have hch : Real.cosh d=1+2*Real.sinh (d/2)^2 := by
    have ha:=Real.cosh_two_mul (d/2)
    have hb:=Real.cosh_sq_sub_sinh_sq (d/2)
    rw [show 2*(d/2)=d by ring] at ha
    nlinarith
  have hlt : Real.cosh T^2-Real.sinh T^2*Real.cosh d <1 := by
    nlinarith [mul_pos (sq_pos_of_pos hsp) (sq_pos_of_pos hsd)]
  have hlow : Real.cosh T^2-Real.sinh T^2*Real.cosh d≤ -1 := by
    rcases (le_abs.mp hgap) with h | h
    · exact (hlt.not_ge h).elim
    · linarith
  have hsquared : 1≤(Real.sinh (d/2)*Real.sinh T)^2 := by
    nlinarith
  change 1≤Real.sinh (d/2)*Real.sinh T
  nlinarith [mul_pos hsd hsp]

end LowDimensionalTopology.Geometry.Hyperbolic
