module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.ParabolicHoroballs
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped OnePoint Quaternion
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- The full physical horosphere in quaternion Euclidean three-space, with its positive
height condition; the tangent boundary point itself is not a point of H3. -/
def horospherePhysicalSurface (w : Mobius.ExtendedComplex) (r : ℝ) : Set quaternionThreeSpace :=
  {q | 0 < quaternionHeight q ∧ match w with
    | OnePoint.infty => quaternionHeight q = r
    | OnePoint.some a => ‖q - quaternionThreePoint a r‖ = r}

/-- Actual horizontal projection as a continuous real-linear map. -/
def quaternionHorizontalCLM : quaternionThreeSpace →L[ℝ] ℂ :=
  ({ toFun := quaternionHorizontal
     map_add' := by intro a b; apply Complex.ext <;> rfl
     map_smul' := by intro t q; apply Complex.ext <;> simp [quaternionHorizontal] } :
    quaternionThreeSpace →ₗ[ℝ] ℂ).toContinuousLinearMap

/-- The genuine complex-horizontal/real-vertical coordinate assembly. -/
def quaternionThreePointCLM : ℂ × ℝ →L[ℝ] quaternionThreeSpace :=
  ({ toFun := fun p => quaternionThreePoint p.1 p.2
     map_add' := by intro a b; apply Subtype.ext; apply Quaternion.ext <;> simp [quaternionThreePoint]
     map_smul' := by
       intro t q
       apply Subtype.ext
       apply Quaternion.ext <;> simp [quaternionThreePoint] } :
    (ℂ × ℝ) →ₗ[ℝ] quaternionThreeSpace).toContinuousLinearMap

@[simp] theorem quaternionHorizontalCLM_apply (q : quaternionThreeSpace) :
    quaternionHorizontalCLM q = quaternionHorizontal q := rfl

@[simp] theorem quaternionThreePointCLM_apply (p : ℂ × ℝ) :
    quaternionThreePointCLM p = quaternionThreePoint p.1 p.2 := rfl

/-- The global stereographic parameter of the tangent sphere based at w. -/
def horosphereFiniteParam (w : ℂ) (r : ℝ) (z : ℂ) : quaternionThreeSpace :=
  quaternionThreePoint (w + (2 * r / (1 + ‖z‖ ^ 2)) • z) (2 * r / (1 + ‖z‖ ^ 2))

/-- Its actual inverse coordinate on positive-height three-space. -/
def horosphereFiniteInverse (w : ℂ) (q : quaternionThreeSpace) : ℂ :=
  (quaternionHeight q)⁻¹ • (quaternionHorizontal q - w)

theorem horosphereFiniteParam_height_pos (w : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    0 < quaternionHeight (horosphereFiniteParam w r z) := by
  change 0 < 2 * r / (1 + ‖z‖ ^ 2)
  positivity

theorem horosphereFiniteParam_norm_sq (w : ℂ) (r : ℝ) (z : ℂ) :
    ‖horosphereFiniteParam w r z - quaternionThreePoint w r‖ ^ 2 = r ^ 2 := by
  have hden : 1 + ‖z‖ ^ 2 ≠ 0 := by positivity
  have he : horosphereFiniteParam w r z - quaternionThreePoint w r =
      quaternionThreePoint ((2 * r / (1 + ‖z‖ ^ 2)) • z) (2 * r / (1 + ‖z‖ ^ 2) - r) := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [horosphereFiniteParam, quaternionThreePoint]
  rw [he, Mobius.quaternionThreePoint_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem horosphereFiniteParam_mem (w : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    horosphereFiniteParam w r z ∈ horospherePhysicalSurface (w : Mobius.ExtendedComplex) r := by
  refine ⟨horosphereFiniteParam_height_pos w r hr z, ?_⟩
  exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp (horosphereFiniteParam_norm_sq w r z)

theorem horosphereFiniteInverse_param (w : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    horosphereFiniteInverse w (horosphereFiniteParam w r z) = z := by
  have hk : 2 * r / (1 + ‖z‖ ^ 2) ≠ 0 := ne_of_gt (by positivity : 0 < 2 * r / (1 + ‖z‖ ^ 2))
  simp only [horosphereFiniteInverse, horosphereFiniteParam, quaternionHeight_threePoint,
    quaternionHorizontal_threePoint, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hk, one_smul]

theorem horosphereFiniteParam_inverse (w : ℂ) (r : ℝ) (hr : 0 < r)
    (q : quaternionThreeSpace) (hq : q ∈ horospherePhysicalSurface (w : Mobius.ExtendedComplex) r) :
    horosphereFiniteParam w r (horosphereFiniteInverse w q) = q := by
  have ht : quaternionHeight q ≠ 0 := hq.1.ne'
  have hn : ‖quaternionHorizontal q - w‖ ^ 2 + (quaternionHeight q - r) ^ 2 = r ^ 2 := by
    have he : q - quaternionThreePoint w r =
        quaternionThreePoint (quaternionHorizontal q - w) (quaternionHeight q - r) := by
      rw [← quaternionThreePoint_coordinates q]
      apply Subtype.ext
      apply Quaternion.ext <;> simp [quaternionThreePoint, quaternionHorizontal, quaternionHeight]
    have hs := congrArg (fun x : ℝ => x ^ 2) hq.2
    rwa [he, Mobius.quaternionThreePoint_norm_sq] at hs
  have hden : 1 + ‖horosphereFiniteInverse w q‖ ^ 2 = 2 * r / quaternionHeight q := by
    simp only [horosphereFiniteInverse, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    field_simp
    nlinarith
  have hk : 2 * r / (1 + ‖horosphereFiniteInverse w q‖ ^ 2) = quaternionHeight q := by
    rw [hden]
    field_simp
  rw [horosphereFiniteParam, hk, horosphereFiniteInverse, smul_smul, mul_inv_cancel₀ ht, one_smul,
    add_sub_cancel]
  exact quaternionThreePoint_coordinates q


/-- The actual stereographic parameter is globally continuously differentiable. -/
theorem horosphereFiniteParam_contDiff (w : ℂ) (r : ℝ) : ContDiff ℝ 1 (horosphereFiniteParam w r) := by
  have hk : ContDiff ℝ 1 (fun z : ℂ => 2 * r / (1 + ‖z‖ ^ 2)) :=
    contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ)) (fun _ => by positivity)
  exact quaternionThreePointCLM.contDiff.comp ((contDiff_const.add (hk.smul contDiff_id)).prodMk hk)

/-- The inverse coordinate is C1 at every actual positive-height point. -/
theorem horosphereFiniteInverse_contDiffAt (w : ℂ) (q : quaternionThreeSpace)
    (hq : quaternionHeight q ≠ 0) : ContDiffAt ℝ 1 (horosphereFiniteInverse w) q :=
  (quaternionHeightContinuous.contDiff.contDiffAt.inv hq).smul
    (quaternionHorizontalCLM.contDiff.contDiffAt.sub contDiffAt_const)

/-- A genuine global coordinate homeomorphism for every finite-based physical horosphere. -/
def horosphereFiniteParamHomeomorph (w : ℂ) (r : ℝ) (hr : 0 < r) :
    ℂ ≃ₜ horospherePhysicalSurface (w : Mobius.ExtendedComplex) r where
  toFun z := ⟨horosphereFiniteParam w r z, horosphereFiniteParam_mem w r hr z⟩
  invFun q := horosphereFiniteInverse w q.val
  left_inv := horosphereFiniteInverse_param w r hr
  right_inv q := Subtype.ext (horosphereFiniteParam_inverse w r hr q.val q.property)
  continuous_toFun := (horosphereFiniteParam_contDiff w r).continuous.subtype_mk _
  continuous_invFun := continuous_iff_continuousAt.mpr (fun q =>
    (horosphereFiniteInverse_contDiffAt w q.val q.property.1.ne').continuousAt.comp
      continuous_subtype_val.continuousAt)

/-- A differentiable left inverse forces injectivity of the genuine ambient differential. -/
theorem horosphere_fderiv_injective_of_leftInverse (f : ℂ → quaternionThreeSpace)
    (g : quaternionThreeSpace → ℂ) (hleft : Function.LeftInverse g f) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g (f z)) :
    Function.Injective (fderiv ℝ f z) := by
  have hc := hg.hasFDerivAt.comp z hf.hasFDerivAt
  have he : g ∘ f = id := funext hleft
  rw [he] at hc
  have hlin : (fderiv ℝ g (f z)).comp (fderiv ℝ f z) = ContinuousLinearMap.id ℝ ℂ :=
    hc.unique (hasFDerivAt_id z)
  have hleft' : Function.LeftInverse (fderiv ℝ g (f z)) (fderiv ℝ f z) := by
    intro v
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hlin
  exact hleft'.injective

/-- The stereographic chart is regular at every point of its full global parameter domain. -/
theorem horosphereFiniteParam_fderiv_injective (w : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    Function.Injective (fderiv ℝ (horosphereFiniteParam w r) z) :=
  horosphere_fderiv_injective_of_leftInverse (horosphereFiniteParam w r) (horosphereFiniteInverse w)
    (horosphereFiniteInverse_param w r hr) z ((horosphereFiniteParam_contDiff w r).differentiable_one z)
    ((horosphereFiniteInverse_contDiffAt w _ (horosphereFiniteParam_height_pos w r hr z).ne').differentiableAt_one)

/-- The global physical parameter for a horosphere based at infinity. -/
def horosphereInftyParam (r : ℝ) (z : ℂ) : quaternionThreeSpace := quaternionThreePoint z r

theorem horosphereInftyParam_contDiff (r : ℝ) : ContDiff ℝ 1 (horosphereInftyParam r) :=
  quaternionThreePointCLM.contDiff.comp (contDiff_id.prodMk contDiff_const)

def horosphereInftyParamHomeomorph (r : ℝ) (hr : 0 < r) : ℂ ≃ₜ horospherePhysicalSurface ∞ r where
  toFun z := ⟨horosphereInftyParam r z, hr, rfl⟩
  invFun q := quaternionHorizontal q.val
  left_inv z := quaternionHorizontal_threePoint z r
  right_inv q := Subtype.ext (by
    change quaternionThreePoint (quaternionHorizontal q.val) r = q.val
    exact (congrArg (quaternionThreePoint (quaternionHorizontal q.val)) q.property.2.symm).trans
      (quaternionThreePoint_coordinates q.val))
  continuous_toFun := (horosphereInftyParam_contDiff r).continuous.subtype_mk _
  continuous_invFun := quaternionHorizontalCLM.continuous.comp continuous_subtype_val

theorem horosphereInftyParam_fderiv_injective (r : ℝ) (z : ℂ) :
    Function.Injective (fderiv ℝ (horosphereInftyParam r) z) :=
  horosphere_fderiv_injective_of_leftInverse (horosphereInftyParam r) quaternionHorizontal
    (fun z => quaternionHorizontal_threePoint z r) z
    ((horosphereInftyParam_contDiff r).differentiable_one z) quaternionHorizontalCLM.differentiableAt

/-- One physical global parameter covering the complete horosphere at every ideal basepoint. -/
def horospherePhysicalParam (w : Mobius.ExtendedComplex) (r : ℝ) : ℂ → quaternionThreeSpace :=
  match w with
  | OnePoint.infty => horosphereInftyParam r
  | OnePoint.some a => horosphereFiniteParam a r

/-- The complete physical horosphere has a genuine global homeomorphism with the plane. -/
def horosphereParamHomeomorph (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    ℂ ≃ₜ horospherePhysicalSurface w r :=
  match w with
  | OnePoint.infty => horosphereInftyParamHomeomorph r hr
  | OnePoint.some a => horosphereFiniteParamHomeomorph a r hr

theorem horosphereParamHomeomorph_coe (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    (horosphereParamHomeomorph w r hr z).val = horospherePhysicalParam w r z := by
  induction w using OnePoint.rec with
  | infty => rfl
  | coe a => rfl

theorem horospherePhysicalParam_contDiff (w : Mobius.ExtendedComplex) (r : ℝ) :
    ContDiff ℝ 1 (horospherePhysicalParam w r) := by
  induction w using OnePoint.rec with
  | infty => exact horosphereInftyParam_contDiff r
  | coe a => exact horosphereFiniteParam_contDiff a r

theorem horospherePhysicalParam_fderiv_injective (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    Function.Injective (fderiv ℝ (horospherePhysicalParam w r) z) := by
  induction w using OnePoint.rec with
  | infty => exact horosphereInftyParam_fderiv_injective r z
  | coe a => exact horosphereFiniteParam_fderiv_injective a r hr z

/-- The global homeomorphism is C1 as a map into the actual ambient Euclidean three-space. -/
theorem horosphereParamHomeomorph_contDiff (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ 1 (fun z => (horosphereParamHomeomorph w r hr z).val) := by
  simpa only [horosphereParamHomeomorph_coe] using horospherePhysicalParam_contDiff w r

/-- The global homeomorphism has an injective actual ambient differential at every point. -/
theorem horosphereParamHomeomorph_fderiv_injective (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    Function.Injective (fderiv ℝ (fun z => (horosphereParamHomeomorph w r hr z).val) z) := by
  simpa only [horosphereParamHomeomorph_coe] using horospherePhysicalParam_fderiv_injective w r hr z

end LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
