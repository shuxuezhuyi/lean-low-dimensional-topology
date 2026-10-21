module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.RayTangents
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped UpperHalfPlane OnePoint Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

theorem HRayAt.mem_iff_upward_of_endpoint_infty {z : ℍ} (R : HRayAt z)
    (hEnd : R.idealEndpoint = ∞) (w : ℍ) :
    w ∈ R.val ↔ w.re = z.re ∧ z.im ≤ w.im := by
  have hL := R.supportLine_of_idealEndpoint_infty hEnd
  have hsign : R.tangentSign = 1 := by
    have h := congrArg Complex.im (R.tangentVector_of_idealEndpoint_infty hEnd)
    simpa only [HRayAt.tangentVector, hL, HalfPlaneLine.tangentAt,
      Complex.smul_im, smul_eq_mul, Complex.I_im, mul_one] using h
  have hforward : R.longitudinal z < R.longitudinal R.directionPoint := by
    by_contra h
    have hs : R.tangentSign = -1 := by rw [HRayAt.tangentSign, ite_eq_right h]
    linarith only [hs, hsign]
  constructor
  · intro hw
    have hline := R.subset_support hw
    have hm := (R.mem_iff_longitudinal hline).mp hw
    rw [ite_eq_left hforward] at hm
    refine ⟨by simpa only [hL, HalfPlaneLine.carrier, mem_ofPred_eq] using hline, ?_⟩
    simpa only [HRayAt.longitudinal, hL, HalfPlaneLine.longitudinal,
      Complex.imCLM_apply, UpperHalfPlane.coe_im] using hm
  · rintro ⟨hre, him⟩
    have hline : w ∈ R.supportLine.carrier := by
      simpa only [hL, HalfPlaneLine.carrier, mem_ofPred_eq] using hre
    apply (R.mem_iff_longitudinal hline).mpr
    rw [ite_eq_left hforward]
    simpa only [HRayAt.longitudinal, hL, HalfPlaneLine.longitudinal,
      Complex.imCLM_apply, UpperHalfPlane.coe_im] using him


/-- A normalizer respecting the specified actual hyperbolic fixed endpoint. -/
theorem realSLMobius_hyperbolic_endpoint_normalizer
    (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : realSLMobius f ≠ 1)
    (ht : 4 < (Matrix.trace f.val)^2) (ξ : Mobius.ExtendedComplex)
    (hξ : (realSLMobius f).val ξ = ξ) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ) (hk : 0 < k), k ≠ 1 ∧
      (realSLMobius s).val ξ = ∞ ∧
      ∀ z : ℍ, (s*f*s⁻¹) • z = verticalDilationSL k hk • z := by
  obtain ⟨a,b,hab,ha,hb,hfix⟩ := realSLMobius_hyperbolic_fixed_pair f hf ht
  have hex : ∃ η : Mobius.ExtendedComplex, η ≠ ξ ∧ η ∈ halfPlaneIdealBoundary ∧
      (realSLMobius f).val η = η := by
    rcases (hfix ξ).mp hξ with rfl | rfl
    · exact ⟨b, hab.symm, hb, (hfix b).mpr (Or.inr rfl)⟩
    · exact ⟨a, hab, ha, (hfix a).mpr (Or.inl rfl)⟩
  obtain ⟨η,hηξ,hηB,hη⟩ := hex
  obtain ⟨s,hsη,hsξ⟩ := realSLMobius_boundary_pair_normalizer η ξ hηB
    (realSLMobius_hyperbolic_fixed_boundary f ht ξ hξ) hηξ
  have hz : (realSLMobius (s*f*s⁻¹)).val (0 : ℂ) = (0 : ℂ) := by
    rw [map_mul,map_mul,map_inv,←hsη]
    change (realSLMobius s).val ((realSLMobius f).val
      ((realSLMobius s).val.symm ((realSLMobius s).val η))) = _
    rw [Equiv.symm_apply_apply,hη]
  have hi : (realSLMobius (s*f*s⁻¹)).val ∞ = ∞ := by
    rw [map_mul,map_mul,map_inv,←hsξ]
    change (realSLMobius s).val ((realSLMobius f).val
      ((realSLMobius s).val.symm ((realSLMobius s).val ξ))) = _
    rw [Equiv.symm_apply_apply,hξ]
  obtain ⟨k,hk,hkg⟩ := realSLMobius_zero_infty_dilation (s*f*s⁻¹) hz hi
  refine ⟨s,k,hk,?_,hsξ,?_⟩
  · intro he
    have hu : Units.mk0 (k : ℂ) (Complex.ofReal_ne_zero.mpr hk.ne') = 1 := by
      apply Units.ext
      simpa using congrArg (fun r : ℝ => (r : ℂ)) he
    rw [hu,DiscreteGroups.mobiusScaling_one,map_mul,map_mul,map_inv] at hkg
    apply hf
    calc
      realSLMobius f = (realSLMobius s)⁻¹ *
          (realSLMobius s * realSLMobius f * (realSLMobius s)⁻¹) * realSLMobius s := by group
      _ = 1 := by rw [hkg];simp
  · intro z
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [←realSLMobius_action,hkg,Mobius.mobiusScaling_coe,verticalDilationSL_coe]
    rfl

/-- The literal Euclidean coordinate action of every actual power of a dilation. -/
theorem hSL_dilation_pow_coe (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ)
    (hk : 0 < k) (hA : ∀ z : ℍ, A • z = verticalDilationSL k hk • z)
    (n : ℕ) (z : ℍ) : (((A^n) • z : ℍ) : ℂ) = (k^n : ℝ) * (z : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_smul,hA,verticalDilationSL_coe,ih]
    push_cast
    rw [pow_succ]
    ring

/-- Actual positive powers are distinct as native hyperbolic isometries. -/
theorem hSL_dilation_powers_injective (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ)
    (hk : 0 < k) (hk1 : k ≠ 1)
    (hA : ∀ z : ℍ, A • z = verticalDilationSL k hk • z) :
    Function.Injective (fun n : ℕ => hSLIsometry (A^n)) := by
  intro m n he
  have hz := congrArg (fun e : ℍ ≃ᵢ ℍ => ((e (metricProbe 0 1 zero_lt_one) : ℍ) : ℂ)) he
  change (((A^m) • metricProbe 0 1 zero_lt_one : ℍ) : ℂ) =
    (((A^n) • metricProbe 0 1 zero_lt_one : ℍ) : ℂ) at hz
  rw [hSL_dilation_pow_coe A k hk hA,hSL_dilation_pow_coe A k hk hA] at hz
  apply (pow_right_injective₀ hk hk1)
  simpa only [←Complex.ofReal_pow,metricProbe,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,mul_one] using congrArg Complex.im hz

/-- Every actual ray to infinity has one genuine compact transversal under an expanding dilation. -/
theorem hSL_expanding_dilation_ray_compact_returns
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ) (hk : 1 < k)
    (hA : ∀ z : ℍ, A • z = verticalDilationSL k (zero_lt_one.trans hk) • z)
    (z : ℍ) (R : HRayAt z) (hR : R.idealEndpoint = ∞) :
    ∃ K : Set ℍ, IsCompact K ∧ ∀ n : ℕ, ((fun w : ℍ => A^n • w) ⁻¹' R.val ∩ K).Nonempty := by
  let φ : ℝ → ℍ := fun t => metricProbe (t*z.re) z.im z.im_pos
  have hφ : Continuous φ := UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (by
    change Continuous (fun t : ℝ => (⟨t*z.re,z.im⟩ : ℂ))
    have he (t : ℝ) : (⟨t*z.re,z.im⟩ : ℂ) = ((t*z.re : ℝ) : ℂ) + (z.im : ℂ)*Complex.I := by
      apply Complex.ext <;> simp
    simp_rw [he]
    fun_prop)
  refine ⟨φ '' Icc (0:ℝ) 1, isCompact_Icc.image hφ, ?_⟩
  intro n
  have hp : 0 < k^n := pow_pos (zero_lt_one.trans hk) n
  have hp1 : 1 ≤ k^n := one_le_pow₀ hk.le
  let t := (k^n)⁻¹
  have ht : t ∈ Icc (0:ℝ) 1 := ⟨inv_nonneg.mpr hp.le, (inv_le_one₀ hp).mpr hp1⟩
  refine ⟨φ t, ?_, ⟨t,ht,rfl⟩⟩
  apply (R.mem_iff_upward_of_endpoint_infty hR _).mpr
  have he := hSL_dilation_pow_coe A k (zero_lt_one.trans hk) hA n (φ t)
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  have hr : (A^n • φ t : ℍ).re = z.re := by
    simpa only [UpperHalfPlane.re,φ,metricProbe,t,←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,mul_inv_cancel_left₀ (ne_of_gt hp)] using hre
  refine ⟨hr,?_⟩
  have hi : (A^n • φ t : ℍ).im = k^n*z.im := by
    simpa only [UpperHalfPlane.im,φ,metricProbe,←Complex.ofReal_pow,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using him
  rw [hi]
  nlinarith only [hp1,z.im_pos]

/-- The actual inverse of a genuine dilation has reciprocal scale. -/
theorem hSL_inverse_dilation_action (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (k : ℝ) (hk : 0 < k)
    (hA : ∀ z : ℍ, A • z = verticalDilationSL k hk • z) :
    ∀ z : ℍ, A⁻¹ • z = verticalDilationSL k⁻¹ (inv_pos.mpr hk) • z := by
  intro z
  apply (hSLIsometry A).injective
  change A • (A⁻¹ • z) = A • (verticalDilationSL k⁻¹ (inv_pos.mpr hk) • z)
  rw [smul_inv_smul,hA]
  apply UpperHalfPlane.ext
  rw [verticalDilationSL_coe,verticalDilationSL_coe]
  push_cast
  rw [←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hk.ne'),one_mul]

/-- Choose exactly the generator or its inverse, expanding toward the specified actual endpoint. -/
theorem realSLMobius_hyperbolic_expanding_endpoint_normalizer
    (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : realSLMobius f ≠ 1)
    (ht : 4 < (Matrix.trace f.val)^2) (ξ : Mobius.ExtendedComplex)
    (hξ : (realSLMobius f).val ξ = ξ) :
    ∃ (B s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ) (hk : 1 < k),
      (B = f ∨ B = f⁻¹) ∧ (realSLMobius s).val ξ = ∞ ∧
      ∀ z : ℍ, (s*B*s⁻¹) • z = verticalDilationSL k (zero_lt_one.trans hk) • z := by
  obtain ⟨s,k,hk,hk1,hsξ,hact⟩ := realSLMobius_hyperbolic_endpoint_normalizer f hf ht ξ hξ
  rcases lt_or_gt_of_ne hk1 with hlt | hgt
  · have hki : 1 < k⁻¹ := (one_lt_inv₀ hk).mpr hlt
    refine ⟨f⁻¹,s,k⁻¹,hki,Or.inr rfl,hsξ,?_⟩
    have he : s*f⁻¹*s⁻¹ = (s*f*s⁻¹)⁻¹ := by group
    rw [he]
    exact hSL_inverse_dilation_action (s*f*s⁻¹) k hk hact
  · exact ⟨f,s,k,hgt,Or.inl rfl,hsξ,hact⟩

/-- Every genuine ray to an actual hyperbolic fixed endpoint returns under distinct genuine
powers to one genuine compact set. The ray may start at any point of the hyperbolic plane. -/
theorem realSL_hyperbolic_fixed_ray_compact_returns
    (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hf : realSLMobius f ≠ 1)
    (ht : 4 < (Matrix.trace f.val)^2) (ξ : Mobius.ExtendedComplex)
    (hξ : (realSLMobius f).val ξ = ξ) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, (B = f ∨ B = f⁻¹) ∧
      Function.Injective (fun n : ℕ => hSLIsometry (B^n)) ∧
      ∀ (z : ℍ) (R : HRayAt z), R.idealEndpoint = ξ →
        ∃ K : Set ℍ, IsCompact K ∧
          ∀ n : ℕ, ((fun w : ℍ => B^n • w) ⁻¹' R.val ∩ K).Nonempty := by
  obtain ⟨B,s,k,hk,hB,hsξ,hact⟩ :=
    realSLMobius_hyperbolic_expanding_endpoint_normalizer f hf ht ξ hξ
  let A := s*B*s⁻¹
  have hinj := hSL_dilation_powers_injective A k (zero_lt_one.trans hk) (ne_of_gt hk) hact
  refine ⟨B,hB,?_,?_⟩
  · intro m n he
    change hSLIsometry (B^m) = hSLIsometry (B^n) at he
    apply hinj
    dsimp only [A]
    rw [conj_pow,conj_pow,hSLIsometry_conjugation,hSLIsometry_conjugation,he]
  · intro z R hR
    let g := Matrix.SpecialLinearGroup.mapGL ℝ s
    have hg : 0 < g.val.det := by simp [g]
    let S := R.realGLMap g
    have hS : S.idealEndpoint = ∞ := by
      rw [HRayAt.realGLMap_idealEndpoint R g hg,hR]
      simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,
        realSLMobius_matrix] using hsξ
    obtain ⟨K₀,hK₀,hmeet⟩ := hSL_expanding_dilation_ray_compact_returns A k hk hact (g • z) S hS
    refine ⟨(hSLIsometry s).symm '' K₀,hK₀.image (hSLIsometry s).symm.continuous,?_⟩
    intro n
    obtain ⟨v,hvR,hvK⟩ := hmeet n
    change A^n • v ∈ S.val at hvR
    change A^n • v ∈ (R.realGLMap g).val at hvR
    rw [← R.realGLMap_carrier g] at hvR
    obtain ⟨u,hu,heu⟩ := hvR
    have heq : B^n • (s⁻¹ • v) = u := by
      apply (hSLIsometry s).injective
      change s • (B^n • (s⁻¹ • v)) = s • u
      have hh : s • (B^n • (s⁻¹ • v)) = A^n • v := by
        dsimp only [A]
        rw [conj_pow]
        simp only [mul_smul]
      rw [hh]
      exact heu.symm
    refine ⟨s⁻¹ • v,?_,?_⟩
    · change B^n • (s⁻¹ • v) ∈ R.val
      rw [heq]
      exact hu
    · exact ⟨v,hvK,rfl⟩

end LowDimensionalTopology.Geometry.Hyperbolic
