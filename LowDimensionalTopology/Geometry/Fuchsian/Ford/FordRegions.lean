/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IsometricCircles
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalConstruction
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
/-! # Actual orbit heights in Ford exteriors

The Ford exterior is the literal common exterior of the matrix isometric
circles. Genuine group translates that both lie in it have equal imaginary
part. This uses the actual fractional-linear action and no angle, cycle or
height conclusion as input.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Fuchsian
open Set LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped UpperHalfPlane MatrixGroups Topology OnePoint
noncomputable section

def realSLDenominator (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) : ℂ :=
  UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) (z:ℂ)

theorem realSL_im_action (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (A • z).im=z.im/Complex.normSq (realSLDenominator A z) := by
  change ((Matrix.SpecialLinearGroup.mapGL ℝ A) • z).im=z.im/Complex.normSq (realSLDenominator A z)
  have h:=z.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ A)
  simpa only [realSLDenominator,Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,abs_one,one_mul] using h


theorem realSL_im_le_of_denominator (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ)
    (hz : 1≤‖realSLDenominator A z‖) : (A • z).im≤z.im := by
  have hs : 1≤Complex.normSq (realSLDenominator A z):=by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith only [hz]
  have hs0 : 0<Complex.normSq (realSLDenominator A z):=by linarith only [hs]
  rw [realSL_im_action]
  apply (div_le_iff₀ hs0).mpr
  nlinarith only [mul_nonneg z.im_pos.le (sub_nonneg.mpr hs)]

/-- For a non-affine determinant-one lift, the norm condition is precisely
membership outside the open disk bounded by its genuine isometric circle. -/
theorem realSLDenominator_ge_one_iff_circle_exterior
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : A 1 0≠0) (z : ℍ) :
    1≤‖realSLDenominator A z‖ ↔
      (z:ℂ)∉Metric.ball (-(A 1 1:ℂ)/(A 1 0:ℂ))
        (_root_.LowDimensionalTopology.Geometry.Mobius.isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1)) := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1:=by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have hdC : (A 0 0:ℂ)*(A 1 1:ℂ)-(A 0 1:ℂ)*(A 1 0:ℂ)=1:=by exact_mod_cast hd
  have hcC : (A 1 0:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hc
  have hcpos : 0<‖(A 1 0:ℂ)‖:=norm_pos_iff.mpr hcC
  have he : realSLDenominator A z=(A 1 0:ℂ)*((z:ℂ)-(-(A 1 1:ℂ)/(A 1 0:ℂ))):=by
    change (A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ)=_
    field_simp
    ring
  rw [Metric.mem_ball,not_lt,_root_.LowDimensionalTopology.Geometry.Mobius.isometricCircleRadius,hdC,norm_one,Real.sqrt_one,
    div_le_iff₀ hcpos,he,norm_mul,dist_eq_norm]
  simp only [mul_comm]

/-- The true real unit translation lifts the same sphere transformation. -/
theorem realSLMobius_unitTranslation : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 := by
  apply mobius_ext_on_halfPlane
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
  norm_num

/-- A discrete group containing a unit parabolic has no dilation in its
infinity stabilizer, so omitted affine circles impose no extra restriction. -/
theorem discrete_unitTranslation_affine_denominator
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (A : Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hc : A 1 0=0) : |A 1 1|=1 := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞
  have hle : K≤H:=fun f hf=>((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞
    f).mp hf).1
  have hKd:=discreteMobius_subgroup_of_le H K hd hle
  have hKE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_of_boundary_fixed K ∞ (fun f=>
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ f.val).mp f.property).2)
  have hTK : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ _).mpr
    ⟨hT,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1⟩
  have hAK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈K:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ _).mpr
    ⟨hA,by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,hc]⟩
  have hno:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_parabolic_no_loxodromic K hKd hKE (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)
    hTK ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr
      one_ne_zero) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hAK
  have hdet : A 0 0*A 1 1=1:=by simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using A.det_coe
  have htr : (Matrix.trace A.val)^2≤4:=by
    by_cases hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=1
    · have he : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=4:=by
        rw [←map_one _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_specialLinearProjection]
        norm_num [Matrix.trace_fin_two]
      have hs:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace A
      rw [hf,he] at hs
      have hr:=congrArg Complex.re hs
      norm_num only [Complex.ofReal_re,Complex.re_ofNat] at hr
      exact hr.ge
    · by_contra hgt
      exact hno ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hf).mpr (lt_of_not_ge
        hgt)).1
  rw [Matrix.trace_fin_two] at htr
  have heq : A 0 0=A 1 1:=by nlinarith only [htr,hdet,sq_nonneg (A 0 0-A 1 1)]
  have hs : (A 1 1)^2=1:=by rw [heq] at hdet; nlinarith only [hdet]
  apply (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp
  simpa only [sq_abs,one_pow] using hs

def fordExterior (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ℍ :=
  {z | ∀ A : G,1≤‖realSLDenominator A.val z‖}

theorem fordExterior_isClosed (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    IsClosed (fordExterior G) := by
  have he : fordExterior G=⋂ A : G,{z : ℍ | 1≤‖realSLDenominator A.val z‖}:=by
    ext z
    simp only [fordExterior,mem_ofPred_eq,mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro A
  apply isClosed_le continuous_const
  unfold realSLDenominator UpperHalfPlane.denom
  fun_prop

/-- Equal orbit heights follow from membership in the actual common circle exterior. -/
theorem fordExterior_orbit_height (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (z w : ℍ) (hz : z∈fordExterior G) (hw : w∈fordExterior G) (horbit : w∈MulAction.orbit G z) :
    w.im=z.im := by
  obtain ⟨A,rfl⟩:=horbit
  have hle:=realSL_im_le_of_denominator A.val z (hz A)
  have hge:=realSL_im_le_of_denominator (A⁻¹).val (A • z) (hw A⁻¹)
  have hinv : ((A⁻¹).val • (A • z):ℍ)=z:=inv_smul_smul A z
  rw [hinv] at hge
  exact le_antisymm hle hge

/-- The literal open common Ford exterior cut by a unit vertical strip. -/
def fordDomain (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (x₀ : ℝ) : Set ℍ :=
  interior (fordExterior G) ∩ {z | x₀<z.re ∧ z.re<x₀+1}

theorem closure_fordDomain_subset_exterior (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (x₀ : ℝ) : closure (fordDomain G x₀)⊆fordExterior G := by
  apply closure_minimal _ (fordExterior_isClosed G)
  intro z hz
  exact interior_subset hz.1

/-- A genuine orbit cycle uses the literal closure and the actual original group action. -/
def fordVertexCycle (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (x₀ : ℝ) (z : ℍ) : Set ℍ :=
  closure (fordDomain G x₀) ∩ MulAction.orbit G z

theorem fordVertexCycle_horizontal (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (x₀ : ℝ) (z : ℍ) (hz : z∈closure (fordDomain G x₀)) :
    fordVertexCycle G x₀ z⊆{w : ℍ | w.im=z.im} := by
  rintro w ⟨hw,horbit⟩
  exact fordExterior_orbit_height G z w (closure_fordDomain_subset_exterior G x₀ hz)
    (closure_fordDomain_subset_exterior G x₀ hw) horbit

/-- The same actual common exterior for the full determinant-one lift of the original Mobius group. -/
def mobiusFordExterior (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set ℍ :=
  fordExterior (H.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius)

/-- Actual original Mobius maps between exterior points preserve height, using a constructed real lift. -/
theorem mobiusFordExterior_image_height (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H)
    (hpres : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (z w : ℍ)
    (hfw : f.val (z:ℂ)=((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hz : z∈mobiusFordExterior H) (hw : w∈mobiusFordExterior H) : w.im=z.im := by
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f hpres
  have hAH : A∈H.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius:=by change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H;simpa only [hA] using hf
  have hAz : A • z=w:=by
    apply UpperHalfPlane.ext
    rw [←hA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hfw
    exact OnePoint.coe_injective hfw
  apply fordExterior_orbit_height (H.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius) z w hz hw
  exact ⟨⟨A,hAH⟩,hAz⟩

def mobiusFordDomain (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (x₀ : ℝ) : Set ℍ :=
  fordDomain (H.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius) x₀

/-- The actual original Mobius orbit in the literal closure of the normalized common-circle exterior strip. -/
def mobiusFordVertexCycle (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (x₀ : ℝ) (z :
  ℍ) : Set ℍ :=
  closure (mobiusFordDomain H x₀) ∩
    {w : ℍ | ((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}

theorem mobiusFordVertexCycle_horizontal (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (x₀ : ℝ) (z : ℍ) (hz : z∈closure (mobiusFordDomain H x₀)) :
    mobiusFordVertexCycle H x₀ z⊆{w : ℍ | w.im=z.im} := by
  rintro w ⟨hw,horbit⟩
  obtain ⟨f,hf⟩:=horbit
  change f.val.val (z:ℂ)=((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hf
  exact mobiusFordExterior_image_height H f.val f.property (hpres f.val f.property) z w hf
    (closure_fordDomain_subset_exterior _ x₀ hz) (closure_fordDomain_subset_exterior _ x₀ hw)

/-- The literal closed common exterior of the genuine non-affine isometric circles.
Affine elements contribute no circle and are absent from this definition. -/
def mobiusFordCircleExterior (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set ℍ :=
  {z | ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H → A
    1 0≠0 →
    (z:ℂ)∉Metric.ball (-(A 1 1:ℂ)/(A 1 0:ℂ))
      (_root_.LowDimensionalTopology.Geometry.Mobius.isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1))}

/-- Under the source's discrete unit-translation normalization, the all-matrix
norm description equals precisely the original finite-circle construction. -/
theorem mobiusFordCircleExterior_eq (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    mobiusFordCircleExterior H=mobiusFordExterior H := by
  ext z
  constructor
  · intro hz A
    have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A.val∈H:=A.property
    by_cases hc : A.val 1 0=0
    · have he:=discrete_unitTranslation_affine_denominator H hd hT A.val hA hc
      change 1≤‖(A.val 1 0:ℂ)*(z:ℂ)+(A.val 1 1:ℂ)‖
      simpa only [hc,Complex.ofReal_zero,zero_mul,zero_add,Complex.norm_real,
        Real.norm_eq_abs,he] using (le_refl (1:ℝ))
    · exact (realSLDenominator_ge_one_iff_circle_exterior A.val hc z).mpr (hz A.val hA hc)
  · intro hz A hA hc
    exact (realSLDenominator_ge_one_iff_circle_exterior A hc z).mp (hz ⟨A,hA⟩)

/-- The original open Ford circle exterior cut by an actual unit vertical strip. -/
def mobiusFordCircleDomain (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (x₀ :
  ℝ) : Set ℍ :=
  interior (mobiusFordCircleExterior H) ∩ {z | x₀<z.re ∧ z.re<x₀+1}

theorem mobiusFordCircleDomain_eq (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (x₀ : ℝ) :
    mobiusFordCircleDomain H x₀=mobiusFordDomain H x₀ := by
  rw [mobiusFordCircleDomain,mobiusFordCircleExterior_eq H hd hT]
  rfl

/-- The source cycle uses the actual original group orbit and the closure of
its literal finite-circle Ford construction. -/
def mobiusFordCircleVertexCycle (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (x₀ :
  ℝ) (z : ℍ) : Set ℍ :=
  closure (mobiusFordCircleDomain H x₀) ∩
    {w : ℍ | ((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}

/-- Every actual vertex cycle in the normalized original Ford construction
lies on one genuine horizontal horocycle. -/
theorem mobiusFordCircleVertexCycle_horizontal (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (x₀ : ℝ) (z : ℍ) (hz : z∈closure (mobiusFordCircleDomain H x₀)) :
    mobiusFordCircleVertexCycle H x₀ z⊆{w : ℍ | w.im=z.im} := by
  rw [mobiusFordCircleDomain_eq H hd hT] at hz
  change closure (mobiusFordCircleDomain H x₀) ∩ _⊆_
  rw [mobiusFordCircleDomain_eq H hd hT]
  exact mobiusFordVertexCycle_horizontal H hpres x₀ z hz

end
end LowDimensionalTopology.Geometry.Fuchsian
