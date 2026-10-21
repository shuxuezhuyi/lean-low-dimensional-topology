/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The source angle is the actual rotation argument in [0,2π). -/
def hPositiveRotationAngle (a b : ℝ) : ℝ :=
  if hRotationAngle a b < 0 then hRotationAngle a b + 2*Real.pi else hRotationAngle a b

theorem hPositiveRotationAngle_mem (a b : ℝ) :
    hPositiveRotationAngle a b ∈ Ico 0 (2*Real.pi) := by
  have hθ := hRotationAngle_mem a b
  have hπ := Real.pi_pos
  unfold hPositiveRotationAngle
  split_ifs with h
  · constructor <;> linarith [hθ.1,hθ.2]
  · constructor <;> linarith [hθ.1,hθ.2]

theorem hPositiveRotationAngle_exp (a b : ℝ) (hu : a^2+b^2=1) :
    Complex.exp (Complex.I*hPositiveRotationAngle a b) = hRotationMultiplier a b := by
  rw [hRotationMultiplier_eq_exp a b hu]
  unfold hPositiveRotationAngle
  split_ifs
  · rw [show Complex.I*((hRotationAngle a b+2*Real.pi : ℝ):ℂ) =
      Complex.I*(hRotationAngle a b:ℂ)+2*Real.pi*Complex.I by push_cast; ring,
      Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  · rfl

theorem hPositiveRotationAngle_sin_half (a b : ℝ) :
    |Real.sin (hPositiveRotationAngle a b/2)| = |Real.sin (hRotationAngle a b/2)| := by
  unfold hPositiveRotationAngle
  split_ifs
  · rw [show (hRotationAngle a b+2*Real.pi)/2 = hRotationAngle a b/2+Real.pi by ring,
      Real.sin_add_pi,abs_neg]
  · rfl

theorem hPositiveRotationAngle_cos_half_sq (a b : ℝ) :
    Real.cos (hPositiveRotationAngle a b/2)^2 = Real.cos (hRotationAngle a b/2)^2 := by
  unfold hPositiveRotationAngle
  split_ifs
  · rw [show (hRotationAngle a b+2*Real.pi)/2 = hRotationAngle a b/2+Real.pi by ring,
      Real.cos_add_pi,neg_sq]
  · rfl

/-- The exact native real-matrix denominator, retained as a complex analytic polynomial. -/
def hSLDenom (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (A 1 0 : ℂ)*z + A 1 1

theorem hSLDenom_ne_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    hSLDenom A z ≠ 0 := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A) z

/-- The literal complex denominator cocycle for native special-linear multiplication. -/
theorem hSLDenom_mul (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    hSLDenom (A*B) z = hSLDenom A (B • z : ℍ) * hSLDenom B z := by
  have hd := hSLDenom_ne_zero B z
  simp only [hSLDenom] at hd ⊢
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  push_cast
  field_simp [hd]
  ring

/-- A real normalizer preserves the elliptic fixed-center denominator exactly, not only its norm. -/
theorem hSLDenom_at_rotation_center (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (a b : ℝ) (hu : a^2+b^2=1) (v : ℍ) (hv : A • v = v)
    (hq : q • v = UpperHalfPlane.I) (hr : q*A*q⁻¹ = hRotationSL a b hu) :
    hSLDenom A v = conj (⟨a,b⟩ : ℂ) := by
  have he : q*A = hRotationSL a b hu*q := by rw [← hr]; group
  have h1 := hSLDenom_mul q A v
  have h2 := hSLDenom_mul (hRotationSL a b hu) q v
  rw [hv,he,h2,hq] at h1
  have hd : hSLDenom (hRotationSL a b hu) UpperHalfPlane.I = conj (⟨a,b⟩ : ℂ) := by
    apply Complex.ext <;> simp [hSLDenom,hRotationSL]
  rw [hd] at h1
  apply mul_left_cancel₀ (hSLDenom_ne_zero q v)
  calc
    hSLDenom q v * hSLDenom A v = conj (⟨a,b⟩ : ℂ) * hSLDenom q v := h1.symm
    _ = hSLDenom q v * conj (⟨a,b⟩ : ℂ) := by ring

/-- The native real matrix differentiates the actual extended Mobius map in its finite chart. -/
theorem realSLMobius_hasDerivAt (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    HasDerivAt (Mobius.finiteComplexPart (realSLMobius A).val) (1/(hSLDenom A z)^2) (z : ℂ) := by
  have hd := hSLDenom_ne_zero A z
  have h := Mobius.fractionalLinear_hasDerivAt
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom A)) z hd
  change HasDerivAt (Mobius.finiteComplexPart (Mobius.fractionalLinear _))
    (((A 0 0 : ℂ)*A 1 1 - (A 0 1 : ℂ)*A 1 0)/(hSLDenom A z)^2) (z : ℂ) at h
  have he : (A 0 0 : ℂ)*A 1 1 - (A 0 1 : ℂ)*A 1 0 = 1 := by
    have he := A.det_coe
    rw [Matrix.det_fin_two] at he
    exact_mod_cast he
  rw [he] at h
  simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action] using h

/-- The finite-chart derivative is the actual rotation multiplier after any real center normalization. -/
theorem realSLMobius_rotation_derivative (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (a b : ℝ) (hu : a^2+b^2=1) (v : ℍ) (hv : A • v = v)
    (hq : q • v = UpperHalfPlane.I) (hr : q*A*q⁻¹ = hRotationSL a b hu) :
    HasDerivAt (Mobius.finiteComplexPart (realSLMobius A).val) (hRotationMultiplier a b) (v : ℂ) := by
  have hd := hSLDenom_at_rotation_center A q a b hu v hv hq hr
  have hn := hRotationParameter_norm a b hu
  have hu0 : (⟨a,b⟩ : ℂ) ≠ 0 := by
    intro he
    rw [he,norm_zero] at hn
    norm_num at hn
  have huc : conj (⟨a,b⟩ : ℂ) ≠ 0 := by
    intro he
    apply hu0
    simpa using congrArg conj he
  have hmul : (⟨a,b⟩ : ℂ) * conj (⟨a,b⟩ : ℂ) = 1 := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> nlinarith [hu]
  have he : 1/(conj (⟨a,b⟩ : ℂ))^2 = hRotationMultiplier a b := by
    dsimp [hRotationMultiplier]
    field_simp
    simpa only [mul_comm] using hmul.symm
  simpa only [hd,he] using realSLMobius_hasDerivAt A v

/-- Conjugation sends the literal real-matrix denominator to the conjugate point denominator. -/
theorem hSLDenom_conj (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    hSLDenom A (conj z) = conj (hSLDenom A z) := by
  simp [hSLDenom]

/-- The actual fixed-center coordinate is the source ratio (z-v)/(z-conj v). -/
theorem hSL_fixed_center_cross_ratio (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (v : ℍ) (hv : A • v = v) (z : ℍ) :
    (((A • z : ℍ) : ℂ)-(v : ℂ)) / (((A • z : ℍ) : ℂ)-conj (v : ℂ)) =
      (conj (hSLDenom A v)/hSLDenom A v) *
        (((z : ℂ)-(v : ℂ))/((z : ℂ)-conj (v : ℂ))) := by
  let F := Auxiliary.Analysis.fractionalLinearMap (A 0 0 : ℂ) (A 0 1) (A 1 0) (A 1 1)
  have hF (w : ℍ) : F w = ((A • w : ℍ) : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    rfl
  have hvf : F v = (v : ℂ) := by rw [hF,hv]
  have hvb : F (conj (v : ℂ)) = conj (v : ℂ) := by
    have h := congrArg conj hvf
    simpa only [F,Auxiliary.Analysis.fractionalLinearMap,map_div₀,map_add,map_mul,Complex.conj_ofReal] using h
  have hdv := hSLDenom_ne_zero A v
  have hdz := hSLDenom_ne_zero A z
  have hdvb : hSLDenom A (conj (v : ℂ)) ≠ 0 := by
    rw [hSLDenom_conj]
    intro he
    apply hdv
    simpa using congrArg conj he
  have hdiff (w : ℂ) (hdw : hSLDenom A w ≠ 0) :
      F z-F w = ((z : ℂ)-w)/(hSLDenom A z*hSLDenom A w) := by
    have h := Auxiliary.Analysis.fractionalLinearMap_sub (A 0 0 : ℂ) (A 0 1) (A 1 0) (A 1 1) z w hdz hdw
    have hdet : (A 0 0 : ℂ)*A 1 1-(A 0 1 : ℂ)*A 1 0=1 := by
      have hdet := A.det_coe
      rw [Matrix.det_fin_two] at hdet
      exact_mod_cast hdet
    simpa only [F,hSLDenom,hdet,one_mul] using h
  have h1 := hdiff v hdv
  have h2 := hdiff (conj (v : ℂ)) hdvb
  rw [hvf,hF] at h1
  rw [hvb,hF,hSLDenom_conj] at h2
  have hzv : (z : ℂ)-conj (v : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.conj_im] at hi
    change z.im = -v.im at hi
    linarith [z.im_pos,v.im_pos]
  rw [h1,h2]
  field_simp

/-- The geometric half-open angle interval makes the actual rotation multiplier unique. -/
theorem rotation_exp_injective_Ico {θ φ : ℝ} (hθ : θ ∈ Ico 0 (2*Real.pi))
    (hφ : φ ∈ Ico 0 (2*Real.pi))
    (he : Complex.exp (Complex.I*θ) = Complex.exp (Complex.I*φ)) : θ = φ := by
  apply Circle.exp_injOn_Ico (a := 0) (b := 2*Real.pi) (by simp) hθ hφ
  apply Subtype.ext
  simpa only [Circle.coe_exp,mul_comm] using he

/-- Every actual elliptic isometry has its source angle, finite-chart derivative and fixed-center ratio. -/
theorem realSLMobius_elliptic_rotation_angle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    ∃ θ : ℝ, θ ∈ Ico 0 (2*Real.pi) ∧
      HasDerivAt (Mobius.finiteComplexPart (realSLMobius A).val) (Complex.exp (Complex.I*θ))
        (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) : ℂ) ∧
      (∀ z : ℍ, let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
        (((A • z : ℍ) : ℂ)-(v : ℂ)) / (((A • z : ℍ) : ℂ)-conj (v : ℂ)) =
          Complex.exp (Complex.I*θ) * (((z : ℂ)-(v : ℂ))/((z : ℂ)-conj (v : ℂ)))) ∧
      (Matrix.trace A.val)^2 = 4*(Real.cos (θ/2))^2 := by
  obtain ⟨q,a,b,hu,hq,_hb,hr⟩ := realSLMobius_elliptic_normal_form A hA
  let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
  have hv : A • v = v := (hSL_elliptic_fixed_iff A _ v).mpr rfl
  have hexp := hPositiveRotationAngle_exp a b hu
  refine ⟨hPositiveRotationAngle a b,hPositiveRotationAngle_mem a b,?_,?_,?_⟩
  · rw [hexp]
    exact realSLMobius_rotation_derivative A q a b hu v hv hq hr
  · intro z
    have hd := hSLDenom_at_rotation_center A q a b hu v hv hq hr
    change (((A • z : ℍ) : ℂ)-(v : ℂ))/(((A • z : ℍ) : ℂ)-conj (v : ℂ)) = _
    rw [hSL_fixed_center_cross_ratio A v hv,hd,hexp]
    have hconj : conj (conj (⟨a,b⟩ : ℂ)) = (⟨a,b⟩ : ℂ) := by simp
    rw [hconj]
    rfl
  · have htr := hSL_trace_conjugation A q
    rw [hr] at htr
    rw [← htr,hRotationAngle_trace,hPositiveRotationAngle_cos_half_sq]

/-- The actual finite-chart derivative selects exactly one angle in the geometric interval. -/
theorem realSLMobius_elliptic_unique_angle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    ∃! θ : ℝ, θ ∈ Ico 0 (2*Real.pi) ∧
      HasDerivAt (Mobius.finiteComplexPart (realSLMobius A).val) (Complex.exp (Complex.I*θ))
        (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) : ℂ) := by
  obtain ⟨θ,hθ,hd,_hcr,_htr⟩ := realSLMobius_elliptic_rotation_angle A hA
  refine ⟨θ,⟨hθ,hd⟩,?_⟩
  intro φ hφ
  exact rotation_exp_injective_Ico hφ.1 hθ (hφ.2.unique hd)

/-- The unique actual elliptic rotation angle in half-open interval. -/
def hEllipticRotationAngle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) : ℝ :=
  (realSLMobius_elliptic_unique_angle A hA).choose

/-- The chosen angle retains the actual derivative, fixed-center ratio and trace identities. -/
theorem hEllipticRotationAngle_spec (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    let θ := hEllipticRotationAngle A hA
    let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    θ ∈ Ico 0 (2*Real.pi) ∧
      HasDerivAt (Mobius.finiteComplexPart (realSLMobius A).val) (Complex.exp (Complex.I*θ)) (v : ℂ) ∧
      (∀ z : ℍ, (((A • z : ℍ) : ℂ)-(v : ℂ)) / (((A • z : ℍ) : ℂ)-conj (v : ℂ)) =
        Complex.exp (Complex.I*θ) * (((z : ℂ)-(v : ℂ))/((z : ℂ)-conj (v : ℂ)))) ∧
      (Matrix.trace A.val)^2 = 4*(Real.cos (θ/2))^2 := by
  obtain ⟨θ,hθ,hd,hcr,htr⟩ := realSLMobius_elliptic_rotation_angle A hA
  have hspec := (realSLMobius_elliptic_unique_angle A hA).choose_spec
  have he : θ = hEllipticRotationAngle A hA := hspec.2 θ ⟨hθ,hd⟩
  rw [← he]
  exact ⟨hθ,hd,hcr,htr⟩

/-- The genuine centered disc coordinate is injective on the native hyperbolic plane. -/
theorem fixed_center_coordinate_injective (v : ℍ) :
    Function.Injective (fun z : ℍ => ((z : ℂ)-(v : ℂ))/((z : ℂ)-conj (v : ℂ))) := by
  have hne (z : ℍ) : (z : ℂ)-conj (v : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.conj_im] at hi
    change z.im = -v.im at hi
    linarith [z.im_pos,v.im_pos]
  intro z w he
  have hcross := (div_eq_div_iff (hne z) (hne w)).mp he
  have hp : ((z : ℂ)-(w : ℂ))*((v : ℂ)-conj (v : ℂ)) = 0 := by
    linear_combination hcross
  have hz : (z : ℂ) = (w : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (hne v))
  exact UpperHalfPlane.ext hz

/-- Equality on the genuine native plane determines the original full Mobius transformations. -/
theorem realSLMobius_eq_of_native_action (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : ∀ z : ℍ, A • z = B • z) : realSLMobius A = realSLMobius B := by
  apply Mobius.mobius_eq_of_agree_triple _ _
    ((UpperHalfPlane.I : ℂ) : Mobius.ExtendedComplex)
    (((metricProbe 0 2 (by norm_num) : ℍ) : ℂ) : Mobius.ExtendedComplex)
    (((metricProbe 1 1 (by norm_num) : ℍ) : ℂ) : Mobius.ExtendedComplex)
  · norm_num [Mobius.TripleDistinct,metricProbe,Complex.ext_iff]
  · rw [realSLMobius_action,realSLMobius_action,h]
  · rw [realSLMobius_action,realSLMobius_action,h]
  · rw [realSLMobius_action,realSLMobius_action,h]

/-- The actual center and source rotation angle completely determine the actual elliptic map. -/
theorem realSLMobius_elliptic_eq_of_center_angle (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (hc : hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) =
      hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB))
    (hθ : hEllipticRotationAngle A hA = hEllipticRotationAngle B hB) :
    realSLMobius A = realSLMobius B := by
  have hpA := hEllipticRotationAngle_spec A hA
  have hpB := hEllipticRotationAngle_spec B hB
  apply realSLMobius_eq_of_native_action
  intro z
  apply fixed_center_coordinate_injective (hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB))
  have heA := hpA.2.2.1 z
  have heB := hpB.2.2.1 z
  rw [hc,hθ] at heA
  exact heA.trans heB.symm

/-- The native center is independent of the actual real-matrix lift. -/
theorem hEllipticCenter_congr (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (he : realSLMobius A = realSLMobius B) :
    hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) =
      hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB) := by
  let v := hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
  have hv : B • v = v := (hSL_elliptic_fixed_iff B _ v).mpr rfl
  have ha : A • v = v := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [← realSLMobius_action,he,realSLMobius_action,hv]
  exact ((hSL_elliptic_fixed_iff A _ v).mp ha).symm

/-- The geometric actual rotation angle is independent of the chosen real special-linear lift. -/
theorem hEllipticRotationAngle_congr (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (he : realSLMobius A = realSLMobius B) :
    hEllipticRotationAngle A hA = hEllipticRotationAngle B hB := by
  have hpA := hEllipticRotationAngle_spec A hA
  have hpB := hEllipticRotationAngle_spec B hB
  have hc := hEllipticCenter_congr A B hA hB he
  have hmap : Mobius.finiteComplexPart (realSLMobius A).val = Mobius.finiteComplexPart (realSLMobius B).val :=
    congrArg (fun f : Mobius.complexMobiusGroup => Mobius.finiteComplexPart f.val) he
  have hdA := hpA.2.1
  rw [hmap,hc] at hdA
  exact rotation_exp_injective_Ico hpA.1 hpB.1 (hdA.unique hpB.2.1)

/-- The actual elliptic transformations are classified by their actual center and source angle. -/
theorem realSLMobius_elliptic_eq_iff_center_angle (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B)) :
    realSLMobius A = realSLMobius B ↔
      hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) =
        hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB) ∧
      hEllipticRotationAngle A hA = hEllipticRotationAngle B hB :=
  ⟨fun he => ⟨hEllipticCenter_congr A B hA hB he,hEllipticRotationAngle_congr A B hA hB he⟩,
    fun he => realSLMobius_elliptic_eq_of_center_angle A B hA hB he.1 he.2⟩

/-- A genuine elliptic transformation has a nonzero rotation angle. -/
theorem hEllipticRotationAngle_pos (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) : 0 < hEllipticRotationAngle A hA := by
  have hp := hEllipticRotationAngle_spec A hA
  have ht := (realSLMobius_elliptic_iff A hA.1).mp hA
  have hn : hEllipticRotationAngle A hA ≠ 0 := by
    intro he
    have htr := hp.2.2.2
    rw [he] at htr
    norm_num at htr
    linarith
  exact lt_of_le_of_ne hp.1.1 hn.symm

end LowDimensionalTopology.Geometry.Hyperbolic
