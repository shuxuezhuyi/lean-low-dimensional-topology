/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementDetermination
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


/-- A real quadratic polynomial with constant absolute value has no nonconstant
coefficients. The conclusion also determines the constant term exactly. -/
theorem quadratic_abs_constant_coefficients (h c t b : ℝ)
    (he : ∀ x : ℝ, |c * (x ^ 2 + h ^ 2) + t * x - b| = 2 * h) :
    c = 0 ∧ t = 0 ∧ |b| = 2 * h := by
  let a := c * h ^ 2 - b
  have hs (x : ℝ) : (c * x ^ 2 + t * x + a) ^ 2 = (2 * h) ^ 2 := by
    have ha : |c * x ^ 2 + t * x + a| = 2 * h := by
      have hq : c * x ^ 2 + t * x + a = c * (x ^ 2 + h ^ 2) + t * x - b := by
        dsimp [a]
        ring
      rw [hq]
      exact he x
    calc
      (c * x ^ 2 + t * x + a) ^ 2 = |c * x ^ 2 + t * x + a| ^ 2 := (sq_abs _).symm
      _ = (2 * h) ^ 2 := congrArg (fun y : ℝ => y ^ 2) ha
  have h0 := hs 0
  have h1 := hs 1
  have hn1 := hs (-1)
  have h2 := hs 2
  have hn2 := hs (-2)
  have hc : c = 0 := by nlinarith [sq_nonneg c]
  have ht : t = 0 := by rw [hc] at h1 hn1; nlinarith [sq_nonneg t]
  refine ⟨hc, ht, ?_⟩
  simpa only [hc, zero_mul, mul_zero, zero_add, sub_zero, zero_sub, abs_neg] using he 0


/-- The actual native displacement determines the original projective map up to inversion. -/
theorem realSLMobius_inverse_pair_of_displacement (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : hSinhDisplacement (hSLIsometry A) = hSinhDisplacement (hSLIsometry B)) :
    realSLMobius A = realSLMobius B ∨ realSLMobius A = (realSLMobius B)⁻¹ := by
  rcases (hSL_sinh_displacement_determines_inverse_pair A B).mp he with h | h
  · left
    apply realSLMobius_eq_of_native_action
    intro z
    exact congrArg (fun f : ℍ ≃ᵢ ℍ => f z) h
  · right
    have hi : hSLIsometry A = hSLIsometry B⁻¹ := h.trans (hSLIsometry_inverse B).symm
    rw [← map_inv]
    apply realSLMobius_eq_of_native_action
    intro z
    exact congrArg (fun f : ℍ ≃ᵢ ℍ => f z) hi

/-- Every actual frontier point satisfies the literal circle-line boundary equation. -/
theorem hCanonicalRegion_frontier_quadratic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace A.val ≠ 0) (z : ℍ) (hz : z ∈ frontier (hCanonicalRegion A)) :
    |hCanonicalQuadratic A z| = 2*z.im := by
  have he : hCanonicalRegion A = {w : ℍ | |hCanonicalQuadratic A w| < 2*w.im} := by
    ext w
    exact hCanonicalRegion_mem_quadratic A ht w
  rw [he] at hz
  exact frontier_lt_subset_eq (continuous_hCanonicalQuadratic A).abs (by fun_prop) hz

/-- The whole horizontal boundary of a nonzero translation region is genuine frontier. -/
theorem hCanonicalRegion_translation_frontier (t : ℝ) (ht : t ≠ 0) (x : ℝ) :
    metricProbe x (|t|/2) (by positivity) ∈ frontier (hCanonicalRegion (hTranslationSL t)) := by
  rw [hCanonicalRegion_translation]
  change metricProbe x (|t|/2) _ ∈ frontier (UpperHalfPlane.im ⁻¹' Ioi (|t|/2))
  rw [← UpperHalfPlane.isOpenMap_im.preimage_frontier_eq_frontier_preimage
    (by fun_prop) (Ioi (|t|/2)),frontier_Ioi]
  simp [metricProbe]

/-- The complete region-to-inverse-pair recovery in the genuine parabolic standard model. -/
theorem hCanonicalRegion_translation_reconstruct (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (t : ℝ) (ht : t ≠ 0) (he : hCanonicalRegion B = hCanonicalRegion (hTranslationSL t)) :
    realSLMobius B = realSLMobius (hTranslationSL t) ∨
      realSLMobius B = (realSLMobius (hTranslationSL t))⁻¹ := by
  have hB : Matrix.trace B.val ≠ 0 := by
    intro hz
    have hh := (hCanonicalRegion_trace_zero_iff B (hTranslationSL t) he).mp hz
    norm_num [Matrix.trace_fin_two,hTranslationSL] at hh
  let h : ℝ := |t|/2
  have hpos : 0 < h := by dsimp [h]; positivity
  have hbound (x : ℝ) : |B 1 0*(x^2+h^2)+(B 1 1-B 0 0)*x-B 0 1| = 2*h := by
    have hp := hCanonicalRegion_translation_frontier t ht x
    rw [← he] at hp
    have hb := hCanonicalRegion_frontier_quadratic B hB (metricProbe x h hpos) hp
    simpa only [hCanonicalQuadratic,metricProbe,UpperHalfPlane.re,UpperHalfPlane.im] using hb
  obtain ⟨hc,hcenter,habs⟩ := quadratic_abs_constant_coefficients h (B 1 0) (B 1 1-B 0 0) (B 0 1) hbound
  have hbabs : |B 0 1| = |t| := by dsimp [h] at habs; linarith
  have hsinh : hSinhDisplacement (hSLIsometry B) = hSinhDisplacement (hSLIsometry (hTranslationSL t)) := by
    funext z
    change Real.sinh (dist z (B • z)/2) = Real.sinh (dist z (hTranslationSL t • z)/2)
    rw [hSL_half_displacement_polynomial,translation_half_displacement]
    rw [hc,show ((B 1 1 : ℂ)-B 0 0)=0 by exact_mod_cast hcenter]
    simp only [Complex.ofReal_zero,zero_mul,zero_add,zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    rw [hbabs]
  exact realSLMobius_inverse_pair_of_displacement B (hTranslationSL t) hsinh

/-- The real-to-complex special-linear embedding loses no actual matrix entries. -/
theorem realSL_complex_embedding_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) Complex.ofRealHom) := by
  intro A B he
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact Complex.ofReal_injective (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℂ => g i j) he)

/-- The only real special-linear lift ambiguity of an actual Mobius transformation is its sign. -/
theorem realSLMobius_eq_iff_sign (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    realSLMobius A = realSLMobius B ↔ B=A ∨ B= -A := by
  constructor
  · intro he
    have hm : Mobius.mobiusSpecialLinearProjection (Matrix.SpecialLinearGroup.map Complex.ofRealHom A) =
        Mobius.mobiusSpecialLinearProjection (Matrix.SpecialLinearGroup.map Complex.ofRealHom B) := he
    rcases (Mobius.specialLinear_sameMobius_iff _ _).mp hm with h | h
    · exact Or.inl (realSL_complex_embedding_injective h)
    · have hneg : Mobius.specialLinearSignChange (Matrix.SpecialLinearGroup.map Complex.ofRealHom A) =
          Matrix.SpecialLinearGroup.map Complex.ofRealHom (-A) := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        simp [Mobius.specialLinearSignChange,Matrix.SpecialLinearGroup.coe_neg]
      rw [hneg] at h
      exact Or.inr (realSL_complex_embedding_injective h)
  · rintro (rfl | rfl)
    · rfl
    · exact (realSLMobius_neg A).symm

/-- Canonical regions depend on the original actual Mobius map, independently of lift choice. -/
theorem hCanonicalRegion_congr (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : realSLMobius A = realSLMobius B) : hCanonicalRegion A = hCanonicalRegion B := by
  rcases (realSLMobius_eq_iff_sign A B).mp he with rfl | rfl
  · rfl
  · exact (hCanonicalRegion_neg A).symm

/-- Simultaneous genuine conjugation neither creates nor removes an inverse-pair ambiguity. -/
theorem realSLMobius_inverse_pair_of_conjugates (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : realSLMobius (q*A*q⁻¹) = realSLMobius (q*B*q⁻¹) ∨
      realSLMobius (q*A*q⁻¹) = (realSLMobius (q*B*q⁻¹))⁻¹) :
    realSLMobius A = realSLMobius B ∨ realSLMobius A = (realSLMobius B)⁻¹ := by
  rcases he with he | he
  · simp only [map_mul,map_inv] at he
    exact Or.inl (mul_left_cancel (mul_right_cancel he))
  · simp only [map_mul,map_inv,mul_inv_rev,inv_inv,mul_assoc] at he
    exact Or.inr (mul_right_cancel (mul_left_cancel he))

/-- The full arbitrary parabolic branch of canonical-region reconstruction. -/
theorem hCanonicalRegion_parabolic_reconstruct (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) (he : hCanonicalRegion A = hCanonicalRegion B) :
    realSLMobius B = realSLMobius A ∨ realSLMobius B = (realSLMobius A)⁻¹ := by
  obtain ⟨q,t,ht,hr⟩ := realSLMobius_parabolic_normal_form A hA
  have hm : realSLMobius (q*A*q⁻¹) = realSLMobius (hTranslationSL t) := by
    rcases hr with hr | hr
    · rw [hr]
    · rw [hr,realSLMobius_neg]
  have hreg : hCanonicalRegion (q*B*q⁻¹) = hCanonicalRegion (hTranslationSL t) := by
    rw [hCanonicalRegion_conjugation,← he,← hCanonicalRegion_conjugation]
    exact hCanonicalRegion_congr _ _ hm
  have hp := hCanonicalRegion_translation_reconstruct (q*B*q⁻¹) t ht hreg
  rw [← hm] at hp
  exact realSLMobius_inverse_pair_of_conjugates B A q hp

/-- Trace zero always represents a genuine elliptic map, rather than the identity. -/
theorem realSLMobius_trace_zero_elliptic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace A.val=0) : Mobius.MobiusElliptic (realSLMobius A) := by
  have h1 : Mobius.mobiusSquaredTrace (1 : Mobius.complexMobiusGroup)=4 := by
    have h := realSLMobius_squaredTrace (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    norm_num [Matrix.trace_fin_two] at h
    exact h
  have hn : realSLMobius A ≠ 1 := by
    intro he
    have htr := realSLMobius_squaredTrace A
    rw [he,h1,ht] at htr
    norm_num at htr
  exact (realSLMobius_elliptic_iff A hn).mpr (by rw [ht]; norm_num)

/-- The source rotation angle of a genuine half-turn is exactly π. -/
theorem hEllipticRotationAngle_halfTurn (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (ht : Matrix.trace A.val=0) :
    hEllipticRotationAngle A hA = Real.pi := by
  have hp := hEllipticRotationAngle_spec A hA
  have htr := hp.2.2.2
  rw [ht] at htr
  have hc : Real.cos (hEllipticRotationAngle A hA/2)=0 := by nlinarith [sq_nonneg (Real.cos (hEllipticRotationAngle A hA/2))]
  have he : hEllipticRotationAngle A hA/2 = Real.pi/2 := by
    apply Real.injOn_cos
    · constructor <;> linarith [hp.1.1,hp.1.2]
    · constructor <;> linarith [Real.pi_pos]
    · rw [hc,Real.cos_pi_div_two]
  linarith

/-- The actual elliptic and actual half-turn center definitions agree. -/
theorem hEllipticCenter_halfTurn (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (ht : Matrix.trace A.val=0) :
    hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA) = hHalfTurnCenter A ht := by
  have hf := (hSL_trace_zero_fixed_iff A ht (hHalfTurnCenter A ht)).mpr rfl
  exact ((hSL_elliptic_fixed_iff A _ _).mp hf).symm

/-- The complete singleton branch of actual canonical-region reconstruction. -/
theorem hCanonicalRegion_halfTurn_reconstruct (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace A.val=0) (he : hCanonicalRegion A = hCanonicalRegion B) :
    realSLMobius A = realSLMobius B := by
  have htB := (hCanonicalRegion_trace_zero_iff A B he).mp ht
  have hA := realSLMobius_trace_zero_elliptic A ht
  have hB := realSLMobius_trace_zero_elliptic B htB
  have hc : hHalfTurnCenter A ht = hHalfTurnCenter B htB := by
    rw [hCanonicalRegion_halfTurn A ht,hCanonicalRegion_halfTurn B htB] at he
    exact Set.singleton_injective he
  apply realSLMobius_elliptic_eq_of_center_angle A B hA hB
  · rw [hEllipticCenter_halfTurn A hA ht,hEllipticCenter_halfTurn B hB htB,hc]
  · rw [hEllipticRotationAngle_halfTurn A hA ht,hEllipticRotationAngle_halfTurn B hB htB]

/-- A real quadratic with the stated linear absolute value on the positive half-line is determined exactly. -/
theorem quadratic_abs_linear_positive_coefficients (c t b : ℝ)
    (he : ∀ y : ℝ, 0 < y → |c*y^2+t*y-b|=2*y) :
    c=0 ∧ b=0 ∧ |t|=2 := by
  have hs (y : ℝ) (hy : 0 < y) : (c*y^2+t*y-b)^2 = (2*y)^2 := by
    calc
      (c*y^2+t*y-b)^2 = |c*y^2+t*y-b|^2 := (sq_abs _).symm
      _ = (2*y)^2 := congrArg (fun x : ℝ => x^2) (he y hy)
  have h1 := hs 1 (by norm_num)
  have h2 := hs 2 (by norm_num)
  have h3 := hs 3 (by norm_num)
  have h4 := hs 4 (by norm_num)
  have h5 := hs 5 (by norm_num)
  have hc : c=0 := by nlinarith [sq_nonneg c]
  have hb : b=0 := by rw [hc] at h1 h2 h3; nlinarith [sq_nonneg b]
  refine ⟨hc,hb,?_⟩
  simpa only [hc,hb,zero_mul,zero_add,sub_zero,mul_one] using he 1 (by norm_num)

/-- A continuous vertical probe transfers a true one-dimensional frontier to the actual plane. -/
theorem vertical_probe_mem_frontier (S : Set ℍ) (x h : ℝ) (hh : 0 < h)
    (he : ∀ s : ℝ, metricProbe x (Real.exp s) (Real.exp_pos s) ∈ S ↔ Real.log h < s) :
    metricProbe x h hh ∈ frontier S := by
  let f : ℝ → ℍ := fun s => metricProbe x (Real.exp s) (Real.exp_pos s)
  have hf : Continuous f := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun s : ℝ => (⟨x,Real.exp s⟩ : ℂ))
    have hc : Continuous (fun s : ℝ => (x : ℂ)+(Real.exp s : ℂ)*Complex.I) := by fun_prop
    have heq : (fun s : ℝ => (⟨x,Real.exp s⟩ : ℂ)) =
        (fun s : ℝ => (x : ℂ)+(Real.exp s : ℂ)*Complex.I) := by
      funext s
      apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        sub_zero,zero_add,add_zero]
    rw [heq]
    exact hc
  have hset : f ⁻¹' S = Ioi (Real.log h) := by
    ext s
    exact he s
  have hp : Real.log h ∈ frontier (f ⁻¹' S) := by rw [hset,frontier_Ioi]; simp
  have hfp := hf.frontier_preimage_subset S hp
  change f (Real.log h) ∈ frontier S at hfp
  simpa only [f,Real.exp_log hh] using hfp

/-- Every nontrivial diagonal boundary ray lies on the genuine frontier. -/
theorem hCanonicalRegion_diagonal_frontier (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (htr : Matrix.trace A.val ≠ 0) (hc : A 1 0=0) (hb : A 0 1=0)
    (x h : ℝ) (hh : 0 < h) (hbound : |(A 1 1-A 0 0)*x|=2*h) :
    metricProbe x h hh ∈ frontier (hCanonicalRegion A) := by
  apply vertical_probe_mem_frontier _ x h hh
  intro s
  rw [hCanonicalRegion_mem_quadratic A htr]
  have he : |hCanonicalQuadratic A (metricProbe x (Real.exp s) (Real.exp_pos s))| = 2*h := by
    simpa only [hCanonicalQuadratic,metricProbe,UpperHalfPlane.re,UpperHalfPlane.im,
      hc,hb,zero_mul,zero_add,sub_zero] using hbound
  rw [he]
  change 2*h < 2*Real.exp s ↔ _
  have hexp : h < Real.exp s ↔ Real.log h < s := by
    conv_lhs => rw [← Real.exp_log hh]
    exact Real.exp_lt_exp
  constructor
  · intro hhs
    exact hexp.mp (by linarith)
  · intro hhs
    have he := hexp.mpr hhs
    linarith

/-- A true diagonal real matrix's canonical region recovers every centered matrix coefficient. -/
theorem hCanonicalRegion_diagonal_coefficients (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (htr : Matrix.trace A.val ≠ 0) (hc : A 1 0=0) (hb : A 0 1=0)
    (ht : A 1 1-A 0 0 ≠ 0) (he : hCanonicalRegion B = hCanonicalRegion A) :
    B 1 0=0 ∧ B 0 1=0 ∧ |B 1 1-B 0 0|=|A 1 1-A 0 0| := by
  let k : ℝ := 2/(A 1 1-A 0 0)
  have hk : k ≠ 0 := div_ne_zero (by norm_num) ht
  have hB : Matrix.trace B.val ≠ 0 := by
    intro hB
    exact htr ((hCanonicalRegion_trace_zero_iff B A he).mp hB)
  have hbound (y : ℝ) (hy : 0 < y) :
      |(B 1 0*(k^2+1))*y^2+((B 1 1-B 0 0)*k)*y-B 0 1|=2*y := by
    have hxy : |(A 1 1-A 0 0)*(k*y)|=2*y := by
      have hh : (A 1 1-A 0 0)*(k*y)=2*y := by dsimp [k]; field_simp
      rw [hh,abs_of_pos (by positivity)]
    have hp := hCanonicalRegion_diagonal_frontier A htr hc hb (k*y) y hy hxy
    rw [← he] at hp
    have hpB := hCanonicalRegion_frontier_quadratic B hB (metricProbe (k*y) y hy) hp
    change |B 1 0*((k*y)^2+y^2)+(B 1 1-B 0 0)*(k*y)-B 0 1|=2*y at hpB
    convert hpB using 2; ring
  obtain ⟨hcB,hbB,htB⟩ := quadratic_abs_linear_positive_coefficients
    (B 1 0*(k^2+1)) ((B 1 1-B 0 0)*k) (B 0 1) hbound
  have hc0 : B 1 0=0 := (mul_eq_zero.mp hcB).resolve_right (by positivity)
  refine ⟨hc0,hbB,?_⟩
  rw [abs_mul] at htB
  have hkabs : |k|=2/|A 1 1-A 0 0| := by dsimp [k]; rw [abs_div]; norm_num
  rw [hkabs] at htB
  have ha := abs_pos.mpr ht
  field_simp at htB
  linarith

/-- A nontrivial actual diagonal model is determined up to inverse by its region. -/
theorem hCanonicalRegion_diagonal_reconstruct (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (htr : Matrix.trace A.val ≠ 0) (hc : A 1 0=0) (hb : A 0 1=0)
    (ht : A 1 1-A 0 0 ≠ 0) (he : hCanonicalRegion B = hCanonicalRegion A) :
    realSLMobius B = realSLMobius A ∨ realSLMobius B = (realSLMobius A)⁻¹ := by
  obtain ⟨hcB,hbB,htB⟩ := hCanonicalRegion_diagonal_coefficients A B htr hc hb ht he
  have hsinh : hSinhDisplacement (hSLIsometry B) = hSinhDisplacement (hSLIsometry A) := by
    funext z
    change Real.sinh (dist z (B • z)/2)=Real.sinh (dist z (A • z)/2)
    rw [hSL_half_displacement_polynomial,hSL_half_displacement_polynomial,hc,hb,hcB,hbB]
    simp only [Complex.ofReal_zero,zero_mul,zero_add,sub_zero,norm_mul,
      ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,htB]
  exact realSLMobius_inverse_pair_of_displacement B A hsinh

/-- A genuine positive dilation meets the exact diagonal reconstruction hypotheses. -/
theorem hCanonicalRegion_dilation_reconstruct (k : ℝ) (hk : 0 < k) (hk1 : k ≠ 1)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : hCanonicalRegion B = hCanonicalRegion (verticalDilationSL k hk)) :
    realSLMobius B = realSLMobius (verticalDilationSL k hk) ∨
      realSLMobius B = (realSLMobius (verticalDilationSL k hk))⁻¹ := by
  let D := verticalDilationSL k hk
  have hc : D 1 0=0 := rfl
  have hb : D 0 1=0 := rfl
  have htr : Matrix.trace D.val ≠ 0 := by
    have htrace : Matrix.trace D.val=Real.sqrt k+1/Real.sqrt k := by
      simp [D,verticalDilationSL,Matrix.trace_fin_two]
    rw [htrace]
    have hp := Real.sqrt_pos.mpr hk
    positivity
  have ht : D 1 1-D 0 0 ≠ 0 := by
    intro hz
    have hfix : D • UpperHalfPlane.I=UpperHalfPlane.I := by
      rw [hSL_fixed_iff]
      rw [hc,hb,show ((D 1 1 : ℂ)-D 0 0)=0 by exact_mod_cast hz]
      simp
    have hi := congrArg UpperHalfPlane.im hfix
    change (verticalDilationSL k hk • UpperHalfPlane.I).im=UpperHalfPlane.I.im at hi
    rw [verticalDilationSL_im] at hi
    exact hk1 (by simpa using hi)
  exact hCanonicalRegion_diagonal_reconstruct D B htr hc hb ht he

/-- The full arbitrary hyperbolic branch of canonical-region reconstruction. -/
theorem hCanonicalRegion_hyperbolic_reconstruct (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (he : hCanonicalRegion A = hCanonicalRegion B) :
    realSLMobius B = realSLMobius A ∨ realSLMobius B = (realSLMobius A)⁻¹ := by
  obtain ⟨q,k,hk,hk1,_hn,hact⟩ := realSLMobius_hyperbolic_normalizer A hA ht
  have hm : realSLMobius (q*A*q⁻¹)=realSLMobius (verticalDilationSL k hk) :=
    realSLMobius_eq_of_native_action _ _ hact
  have hreg : hCanonicalRegion (q*B*q⁻¹)=hCanonicalRegion (verticalDilationSL k hk) := by
    rw [hCanonicalRegion_conjugation,← he,← hCanonicalRegion_conjugation]
    exact hCanonicalRegion_congr _ _ hm
  have hp := hCanonicalRegion_dilation_reconstruct k hk hk1 (q*B*q⁻¹) hreg
  rw [← hm] at hp
  exact realSLMobius_inverse_pair_of_conjugates B A q hp

/-- Four genuine circle extremal probes recover a linear boundary expression without a sign assumption. -/
theorem circle_four_probe_coefficients (h r u t v : ℝ) (hr : 0 < r)
    (htop : |u*(h+r)-v|=2*(h+r)) (hbot : |u*(h-r)-v|=2*(h-r))
    (hleft : |u*h+t*r-v|=2*h) (hright : |u*h-t*r-v|=2*h) :
    t=0 ∧ v=0 ∧ |u|=2 := by
  have hL := congrArg (fun x : ℝ => x^2) hleft
  have hR := congrArg (fun x : ℝ => x^2) hright
  simp only [sq_abs] at hL hR
  have ht : t=0 := by
    by_contra ht
    have hp : t*r*(u*h-v)=0 := by linear_combination (hL-hR)/4
    have hv : u*h-v=0 := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero ht hr.ne')
    have hp : u*(h+r)-v=u*r := by nlinarith [hv]
    have hm : u*(h-r)-v= -(u*r) := by nlinarith [hv]
    rw [hp] at htop
    rw [hm,abs_neg] at hbot
    linarith
  have hM := congrArg (fun x : ℝ => x^2) htop
  have hm := congrArg (fun x : ℝ => x^2) hbot
  simp only [sq_abs] at hM hm
  rw [ht,zero_mul,add_zero] at hL
  have hus : r^2*(u^2-4)=0 := by linear_combination (hM+hm)/2-hL
  have hu : u^2=4 := by
    have hh := (mul_eq_zero.mp hus).resolve_left (pow_ne_zero 2 hr.ne')
    linarith
  have hu0 : u ≠ 0 := by intro he; rw [he] at hu; norm_num at hu
  have hprod : r*(u*v)=0 := by linear_combination h*r*hu-(hM-hm)/4
  have hv : v=0 := (mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hr.ne')).resolve_left hu0
  refine ⟨ht,hv,?_⟩
  apply (sq_eq_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).mp
  rw [sq_abs,hu]
  norm_num

/-- The exact source standard elliptic canonical region is also a literal Euclidean circle disc. -/
theorem hCanonicalRegion_rotation_euclidean_ball (a b : ℝ) (hu : a^2+b^2=1)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    hCanonicalRegion (hRotationSL a b hu) =
      {z : ℍ | (z : ℂ) ∈ Metric.ball (⟨0,1/|b|⟩ : ℂ) (|a|/|b|)} := by
  let w : ℝ := |b|
  let H : ℝ := 1/w
  let r : ℝ := |a|/w
  have hw : 0 < w := abs_pos.mpr hb
  have hr : 0 < r := div_pos (abs_pos.mpr ha) hw
  have hWH : w*H=1 := by dsimp [H]; field_simp
  have hGeom : H^2-r^2=1 := by
    dsimp [H,r,w]
    simp only [div_pow,one_pow,sq_abs]
    field_simp [hb]
    nlinarith [hu]
  have ht : Matrix.trace (hRotationSL a b hu).val ≠ 0 := by
    simpa [Matrix.trace_fin_two,hRotationSL] using ha
  ext z
  rw [hCanonicalRegion_mem_quadratic _ ht]
  have hq : hCanonicalQuadratic (hRotationSL a b hu) z = -b*(z.re^2+z.im^2+1) := by
    simp only [hCanonicalQuadratic,hRotationSL,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  have hPos : 0 < z.re^2+z.im^2+1 := by nlinarith [sq_nonneg z.re,sq_nonneg z.im]
  rw [hq,abs_mul,abs_neg,abs_of_pos hPos]
  change w*(z.re^2+z.im^2+1)<2*z.im ↔ (z : ℂ) ∈ Metric.ball (⟨0,H⟩ : ℂ) r
  rw [Metric.mem_ball,dist_eq_norm,← sq_lt_sq₀ (norm_nonneg _) hr.le]
  have hN : ‖(z : ℂ)-(⟨0,H⟩ : ℂ)‖^2=z.re^2+(z.im-H)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
      sub_zero]
    ring
  rw [hN]
  have hDiff : w*(z.re^2+(z.im-H)^2-r^2)=w*(z.re^2+z.im^2+1)-2*z.im := by
    linear_combination w*hGeom-2*z.im*hWH
  have hs := mul_lt_mul_iff_right₀ (a := w) (b := z.re^2+(z.im-H)^2-r^2) (c := 0) hw
  rw [mul_zero,hDiff] at hs
  simpa only [sub_neg] using hs

/-- The four genuine extremal points of the standard elliptic circle recover its matrix coefficients. -/
theorem hCanonicalRegion_rotation_coefficients (a b : ℝ) (hu : a^2+b^2=1)
    (ha : a ≠ 0) (hb : b ≠ 0) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : hCanonicalRegion B = hCanonicalRegion (hRotationSL a b hu)) :
    B 1 1-B 0 0=0 ∧ B 0 1= -B 1 0 ∧ |B 1 0|=|b| := by
  let H : ℝ := 1/|b|
  let r : ℝ := |a|/|b|
  have hw : 0 < |b| := abs_pos.mpr hb
  have hH : 0 < H := one_div_pos.mpr hw
  have hr : 0 < r := div_pos (abs_pos.mpr ha) hw
  have hWH : H*|b|=1 := by dsimp [H]; field_simp
  have hGeom : H^2-r^2=1 := by
    dsimp [H,r]
    simp only [div_pow,one_pow,sq_abs]
    field_simp [hb]
    nlinarith [hu]
  have ha1 : |a| < 1 := by
    apply (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [sq_abs]
    nlinarith [sq_pos_of_ne_zero hb]
  have hrH : r < H := by
    apply (div_lt_div_iff₀ hw hw).mpr
    nlinarith [ha1]
  have htr : Matrix.trace (hRotationSL a b hu).val ≠ 0 := by
    simpa [Matrix.trace_fin_two,hRotationSL] using ha
  have hB : Matrix.trace B.val ≠ 0 := by
    intro htB
    exact htr ((hCanonicalRegion_trace_zero_iff B _ he).mp htB)
  have hbound (x y : ℝ) (hy : 0 < y) (hcirc : x^2+(y-H)^2=r^2) :
      |(2*H*B 1 0)*y+(B 1 1-B 0 0)*x-(B 1 0+B 0 1)|=2*y := by
    let z := metricProbe x y hy
    have hp : z ∈ frontier (hCanonicalRegion (hRotationSL a b hu)) := by
      rw [hCanonicalRegion_rotation_euclidean_ball a b hu ha hb]
      change z ∈ frontier (((↑) : ℍ → ℂ) ⁻¹' Metric.ball (⟨0,H⟩ : ℂ) r)
      rw [← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
        UpperHalfPlane.continuous_coe (Metric.ball (⟨0,H⟩ : ℂ) r),frontier_ball _ hr.ne']
      change dist (z : ℂ) (⟨0,H⟩ : ℂ)=r
      rw [dist_eq_norm]
      apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
      change ‖(⟨x,y⟩ : ℂ)-(⟨0,H⟩ : ℂ)‖^2=r^2
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,sub_zero]
      nlinarith [hcirc]
    rw [← he] at hp
    have hq := hCanonicalRegion_frontier_quadratic B hB z hp
    change |B 1 0*(x^2+y^2)+(B 1 1-B 0 0)*x-B 0 1|=2*y at hq
    have hn : x^2+y^2=2*H*y-1 := by nlinarith [hcirc,hGeom]
    rw [hn] at hq
    convert hq using 2; ring
  have hTop := hbound 0 (H+r) (by positivity) (by ring)
  have hBot := hbound 0 (H-r) (by linarith) (by ring)
  have hLeft := hbound r H hH (by ring)
  have hRight := hbound (-r) H hH (by ring)
  have hcoeff := circle_four_probe_coefficients H r (2*H*B 1 0) (B 1 1-B 0 0) (B 1 0+B 0 1) hr
    (by simpa only [mul_zero,add_zero] using hTop)
    (by simpa only [mul_zero,add_zero] using hBot) hLeft (by simpa only [mul_neg,sub_eq_add_neg] using hRight)
  refine ⟨hcoeff.1,by linarith [hcoeff.2.1],?_⟩
  have hAbs := hcoeff.2.2
  rw [abs_mul,abs_mul,abs_of_pos hH] at hAbs
  norm_num at hAbs
  apply mul_left_cancel₀ hH.ne'
  nlinarith [hWH]

/-- The exact non-half-turn elliptic standard region determines the actual map up to inversion. -/
theorem hCanonicalRegion_rotation_reconstruct (a b : ℝ) (hu : a^2+b^2=1)
    (ha : a ≠ 0) (hb : b ≠ 0) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : hCanonicalRegion B = hCanonicalRegion (hRotationSL a b hu)) :
    realSLMobius B = realSLMobius (hRotationSL a b hu) ∨
      realSLMobius B = (realSLMobius (hRotationSL a b hu))⁻¹ := by
  obtain ⟨htB,hbB,hcB⟩ := hCanonicalRegion_rotation_coefficients a b hu ha hb B he
  have hsinh : hSinhDisplacement (hSLIsometry B) = hSinhDisplacement (hSLIsometry (hRotationSL a b hu)) := by
    funext z
    change Real.sinh (dist z (B • z)/2)=Real.sinh (dist z (hRotationSL a b hu • z)/2)
    rw [hSL_half_displacement_polynomial,hSL_half_displacement_polynomial]
    have hPB : (B 1 0 : ℂ)*(z : ℂ)^2+((B 1 1 : ℂ)-B 0 0)*z-B 0 1 =
        (B 1 0 : ℂ)*((z : ℂ)^2+1) := by
      rw [show ((B 1 1 : ℂ)-B 0 0)=0 by exact_mod_cast htB,hbB]
      push_cast
      ring
    have hPA : ((hRotationSL a b hu) 1 0 : ℂ)*(z : ℂ)^2+
        (((hRotationSL a b hu) 1 1 : ℂ)-(hRotationSL a b hu) 0 0)*z-(hRotationSL a b hu) 0 1 =
        -(b : ℂ)*((z : ℂ)^2+1) := by simp [hRotationSL]; ring
    rw [hPB,hPA,norm_mul,norm_mul,norm_neg,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,hcB]
  exact realSLMobius_inverse_pair_of_displacement B (hRotationSL a b hu) hsinh

/-- The full arbitrary elliptic branch, including the genuine singleton half-turn. -/
theorem hCanonicalRegion_elliptic_reconstruct (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (he : hCanonicalRegion A = hCanonicalRegion B) :
    realSLMobius B = realSLMobius A ∨ realSLMobius B = (realSLMobius A)⁻¹ := by
  by_cases ht : Matrix.trace A.val=0
  · exact Or.inl (hCanonicalRegion_halfTurn_reconstruct A B ht he).symm
  · obtain ⟨q,a,b,hu,_hq,hb,hr⟩ := realSLMobius_elliptic_normal_form A hA
    have hm : realSLMobius (q*A*q⁻¹)=realSLMobius (hRotationSL a b hu) := by rw [hr]
    have ha : a ≠ 0 := by
      intro ha
      have htr := hSL_trace_conjugation A q
      rw [hr] at htr
      have hz : Matrix.trace (hRotationSL a b hu).val=0 := by simp [Matrix.trace_fin_two,hRotationSL,ha]
      exact ht (htr.symm.trans hz)
    have hreg : hCanonicalRegion (q*B*q⁻¹)=hCanonicalRegion (hRotationSL a b hu) := by
      rw [hCanonicalRegion_conjugation,← he,← hCanonicalRegion_conjugation,hr]
    have hp := hCanonicalRegion_rotation_reconstruct a b hu ha hb (q*B*q⁻¹) hreg
    rw [← hm] at hp
    exact realSLMobius_inverse_pair_of_conjugates B A q hp

/-- A genuine canonical region determines exactly its actual inverse pair. -/
theorem hCanonicalRegion_reconstruct (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (he : hCanonicalRegion A = hCanonicalRegion B) :
    realSLMobius B = realSLMobius A ∨ realSLMobius B = (realSLMobius A)⁻¹ := by
  rcases lt_trichotomy ((Matrix.trace A.val)^2) 4 with ht | ht | ht
  · exact hCanonicalRegion_elliptic_reconstruct A B ((realSLMobius_elliptic_iff A hA).mpr ht) he
  · exact hCanonicalRegion_parabolic_reconstruct A B ((realSLMobius_parabolic_iff A hA).mpr ht) he
  · exact hCanonicalRegion_hyperbolic_reconstruct A B hA ht he

/-- Both directions of the source actual inverse-pair characterization, including projective lift independence. -/
theorem hCanonicalRegion_eq_iff_inverse_pair (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) :
    hCanonicalRegion A = hCanonicalRegion B ↔
      realSLMobius B = realSLMobius A ∨ realSLMobius B = (realSLMobius A)⁻¹ := by
  refine ⟨hCanonicalRegion_reconstruct A B hA,?_⟩
  rintro (he | he)
  · exact (hCanonicalRegion_congr B A he).symm
  · have heq : realSLMobius B=realSLMobius A⁻¹ := by simpa only [map_inv] using he
    exact (hCanonicalRegion_congr B A⁻¹ heq).trans (hCanonicalRegion_inverse A) |>.symm

end LowDimensionalTopology.Geometry.Hyperbolic
