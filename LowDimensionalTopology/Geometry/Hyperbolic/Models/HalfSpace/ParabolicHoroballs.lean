module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenApplications
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups

/-- The actual Euclidean model: tangent open ball at a finite ideal point, or upper horizontal half-space at infinity. -/
def horoballRegion (w : Mobius.ExtendedComplex) (r : ℝ) : Set UpperHalfSpace :=
  match w with
  | OnePoint.infty => {x | r < quaternionHeight x.val}
  | OnePoint.some z => {x | dist x.val (quaternionThreePoint z r) < r}

/-- A genuine horoball based at its specified ideal point, in physical upper-half-space coordinates. -/
def IsHoroballBasedAt (D : Set UpperHalfSpace) (w : Mobius.ExtendedComplex) : Prop :=
  ∃ r : ℝ, 0 < r ∧ D = horoballRegion w r

/-- The source horoball notion uses the actual Euclidean tangent-ball and half-space models. -/
def IsHoroball (D : Set UpperHalfSpace) : Prop := ∃ w, IsHoroballBasedAt D w

/-- A horosphere is the topological boundary of an actual horoball inside H3. -/
def IsHorosphere (S : Set UpperHalfSpace) : Prop := ∃ D, IsHoroball D ∧ S = frontier D

/-- The ideal-infinity model is exactly an upper horizontal half-space. -/
theorem horoballRegion_infty (r : ℝ) : horoballRegion ∞ r = {x | r < quaternionHeight x.val} := rfl

/-- The finite ideal model is exactly an actual Euclidean open tangent ball. -/
theorem horoballRegion_coe (z : ℂ) (r : ℝ) :
    horoballRegion (z : Mobius.ExtendedComplex) r = {x | dist x.val (quaternionThreePoint z r) < r} := rfl

/-- The genuine displacement sublevel is defined using the original hyperbolic path distance. -/
def parabolicDisplacementSublevel (f : Mobius.complexMobiusGroup) (k : ℝ) : Set UpperHalfSpace :=
  {x | Real.sinh (Mobius.upperHalfSpacePathDist x (f • x) / 2) < k}

/-- The canonical one-half displacement sublevel. -/
def canonicalParabolicHoroball (f : Mobius.complexMobiusGroup) : Set UpperHalfSpace :=
  parabolicDisplacementSublevel f (1 / 2)

/-- Conjugation and the actual H3 isometry action transport every displacement exactly. -/
theorem parabolicDisplacement_conjugation (f h : Mobius.complexMobiusGroup) (x : UpperHalfSpace) :
    Mobius.upperHalfSpacePathDist (h • x) ((h * f * h⁻¹) • (h • x)) = Mobius.upperHalfSpacePathDist x (f • x) := by
  simp only [mul_smul, inv_smul_smul, Mobius.upperHalfSpacePathDist_smul]

/-- Every positive-threshold sublevel transforms by actual conjugation; the equality itself holds for all thresholds. -/
theorem parabolicDisplacementSublevel_image (f h : Mobius.complexMobiusGroup) (k : ℝ) :
    (fun x : UpperHalfSpace => h • x) '' parabolicDisplacementSublevel f k =
      parabolicDisplacementSublevel (h * f * h⁻¹) k := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Real.sinh (Mobius.upperHalfSpacePathDist (h • x) ((h * f * h⁻¹) • (h • x)) / 2) < k
    rwa [parabolicDisplacement_conjugation]
  · intro hy
    refine ⟨h⁻¹ • y, ?_, smul_inv_smul h y⟩
    change Real.sinh (Mobius.upperHalfSpacePathDist (h⁻¹ • y) (f • (h⁻¹ • y)) / 2) < k
    have hd := parabolicDisplacement_conjugation f h (h⁻¹ • y)
    simp only [smul_inv_smul] at hd
    rwa [← hd]

/-- For the original canonical sublevel sets. -/
theorem canonicalParabolicHoroball_image (f h : Mobius.complexMobiusGroup) :
    (fun x : UpperHalfSpace => h • x) '' canonicalParabolicHoroball f =
      canonicalParabolicHoroball (h * f * h⁻¹) := parabolicDisplacementSublevel_image f h _

/-- The sharp parabolic-pair displacement bound separates their canonical sublevel sets. -/
theorem canonicalParabolicHoroball_disjoint (f g : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f) (hg : Mobius.MobiusParabolic g)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)))
    (hH : DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup))) :
    Disjoint (canonicalParabolicHoroball f) (canonicalParabolicHoroball g) := by
  apply Set.disjoint_left.mpr
  intro x hfx hgx
  have hb := DiscreteGroups.quarter_le_parabolic_sinh_displacement_product f g hf hg hD hH x
  change Real.sinh (Mobius.upperHalfSpacePathDist x (f • x) / 2) < 1 / 2 at hfx
  change Real.sinh (Mobius.upperHalfSpacePathDist x (g • x) / 2) < 1 / 2 at hgx
  have hfn : 0 ≤ Real.sinh (Mobius.upperHalfSpacePathDist x (f • x) / 2) :=
    Real.sinh_nonneg_iff.mpr (div_nonneg (DiscreteGroups.jorgensen_upperHalfSpacePathDist_nonneg _ _) (by norm_num))
  have hgn : 0 ≤ Real.sinh (Mobius.upperHalfSpacePathDist x (g • x) / 2) :=
    Real.sinh_nonneg_iff.mpr (div_nonneg (DiscreteGroups.jorgensen_upperHalfSpacePathDist_nonneg _ _) (by norm_num))
  nlinarith

/-- Distinct ideal fixed points of two parabolics in a discrete group force disjoint canonical sets. -/
theorem canonicalParabolicHoroball_disjoint_of_no_common_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (f g : Mobius.complexMobiusGroup) (hfH : f ∈ H) (hgH : g ∈ H)
    (hf : Mobius.MobiusParabolic f) (hg : Mobius.MobiusParabolic g) (hn : ¬Mobius.MobiusCommonFixedPoint f g) :
    Disjoint (canonicalParabolicHoroball f) (canonicalParabolicHoroball g) := by
  let K := Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)
  have hfK : f ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgK : g ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hle : K ≤ H := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hfH
    · exact Set.mem_singleton_iff.mp hx ▸ hgH
  let _ : DiscreteTopology H := hD
  have hDK : Mobius.IsDiscreteMobiusSubgroup K := DiscreteGroups.MatrixGroups.subgroup_discrete hle
  have hNK : DiscreteGroups.IsNonElementary K := by
    intro he
    obtain ⟨a, _, hall⟩ := DiscreteGroups.elementary_parabolic_common_fixedPoint K he f hfK hf
    apply hn
    exact ⟨a, hall ⟨f, hfK⟩, hall ⟨g, hgK⟩⟩
  exact canonicalParabolicHoroball_disjoint f g hf hg hDK hNK

/-- The source family contains precisely the canonical sets of actual parabolic subgroup elements. -/
def canonicalParabolicHoroballFamily (H : Subgroup Mobius.complexMobiusGroup) : Set (Set UpperHalfSpace) :=
  {D | ∃ f ∈ H, Mobius.MobiusParabolic f ∧ D = canonicalParabolicHoroball f}

/-- The actual subgroup action permutes the entire family of canonical parabolic sublevel sets. -/
theorem canonicalParabolicHoroballFamily_image (H : Subgroup Mobius.complexMobiusGroup) (h : H) :
    (fun D : Set UpperHalfSpace => (fun x : UpperHalfSpace => h.val • x) '' D) ''
      canonicalParabolicHoroballFamily H = canonicalParabolicHoroballFamily H := by
  ext D
  constructor
  · rintro ⟨E, ⟨f, hf, hpf, rfl⟩, rfl⟩
    refine ⟨h.val * f * h.val⁻¹, H.mul_mem (H.mul_mem h.property hf) (H.inv_mem h.property),
      (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨h.val, rfl⟩)).mp hpf, ?_⟩
    exact canonicalParabolicHoroball_image f h.val
  · rintro ⟨f, hf, hpf, rfl⟩
    let g := h.val⁻¹ * f * h.val
    have hgH : g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem h.property) hf) h.property
    have hpg : Mobius.MobiusParabolic g :=
      (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨h.val⁻¹, by simp [g]⟩)).mp hpf
    refine ⟨canonicalParabolicHoroball g, ⟨g, hgH, hpg, rfl⟩, ?_⟩
    change (fun x : UpperHalfSpace => h.val • x) '' canonicalParabolicHoroball g = canonicalParabolicHoroball f
    rw [canonicalParabolicHoroball_image]
    congr 1
    dsimp [g]
    group

/-- as exact canonical-set equivariance and ideal-base separation. -/
theorem canonicalParabolicHoroballFamily_invariant_and_disjoint_of_no_commonFixedPoint (H : Subgroup
  Mobius.complexMobiusGroup) (hD : Mobius.IsDiscreteMobiusSubgroup H) :
    (∀ h : H, (fun D : Set UpperHalfSpace => (fun x : UpperHalfSpace => h.val • x) '' D) ''
      canonicalParabolicHoroballFamily H = canonicalParabolicHoroballFamily H) ∧
    ∀ f ∈ H, ∀ g ∈ H, Mobius.MobiusParabolic f → Mobius.MobiusParabolic g →
      ¬Mobius.MobiusCommonFixedPoint f g → Disjoint (canonicalParabolicHoroball f) (canonicalParabolicHoroball g) := by
  exact ⟨canonicalParabolicHoroballFamily_image H, fun f hf g hg hpf hpg hn =>
    canonicalParabolicHoroball_disjoint_of_no_common_fixed H hD f g hf hg hpf hpg hn⟩

/-- The original translation is precisely its actual affine Mobius map. -/
theorem parabolic_mobiusTranslation_eq_affine (b : ℂ) :
    DiscreteGroups.mobiusTranslation b = Mobius.affineMobius 1 b one_ne_zero := by
  rfl

/-- Translation in the genuine upper-half-space model leaves height fixed and shifts its horizontal coordinate. -/
theorem parabolic_translation_smul (b : ℂ) (x : UpperHalfSpace) :
    (DiscreteGroups.mobiusTranslation b • x).val =
      quaternionThreePoint (quaternionHorizontal x.val + b) (quaternionHeight x.val) := by
  rw [parabolic_mobiusTranslation_eq_affine, Mobius.affineMobius_smul]
  simp only [one_mul, norm_one]

/-- The horizontal translation difference has its original Euclidean complex length. -/
theorem parabolic_translation_difference_norm (b : ℂ) (x : UpperHalfSpace) :
    ‖x.val - (DiscreteGroups.mobiusTranslation b • x).val‖ = ‖b‖ := by
  have he : x.val - (DiscreteGroups.mobiusTranslation b • x).val = quaternionThreePoint (-b) 0 := by
    rw [parabolic_translation_smul, ← quaternionThreePoint_coordinates x.val]
    apply Subtype.ext
    apply Quaternion.ext <;> simp [quaternionThreePoint, quaternionHorizontal, quaternionHeight]
  rw [he]
  have hb := complexQuaternionBoundary.norm_map (-b)
  change ‖quaternionThreePoint (-b) 0‖ = ‖-b‖ at hb
  simpa only [norm_neg] using hb

/-- The exact generic half-space cosh formula holds in the original quaternion coordinates. -/
theorem parabolic_upperHalfSpacePathDist_cosh (x y : UpperHalfSpace) :
    Real.cosh (Mobius.upperHalfSpacePathDist x y) =
      1 + ‖x.val - y.val‖ ^ 2 / (2 * quaternionHeight x.val * quaternionHeight y.val) := by
  have hn : ‖euclideanThreeQuaternion.symm x.val - euclideanThreeQuaternion.symm y.val‖ =
      ‖x.val - y.val‖ := by
    simpa only [map_sub] using euclideanThreeQuaternion.symm.norm_map (x.val - y.val)
  rw [Mobius.upperHalfSpacePathDist, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpacePathDist_cosh
    (by norm_num : 1 ≤ 2),
    Mobius.upperHalfSpaceHyperbolicHomeomorph_val, Mobius.upperHalfSpaceHyperbolicHomeomorph_val,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpaceHeight_apply, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpaceHeight_apply,
    Mobius.euclideanThreeQuaternion_symm_height, Mobius.euclideanThreeQuaternion_symm_height, hn]

/-- The actual translation has the exact displacement sublevel formula at every point. -/
theorem parabolic_translation_sinh_displacement (b : ℂ) (x : UpperHalfSpace) :
    Real.sinh (Mobius.upperHalfSpacePathDist x (DiscreteGroups.mobiusTranslation b • x) / 2) =
      ‖b‖ / (2 * quaternionHeight x.val) := by
  let t := quaternionHeight x.val
  let d := Mobius.upperHalfSpacePathDist x (DiscreteGroups.mobiusTranslation b • x)
  have ht : 0 < t := x.property
  have hc := parabolic_upperHalfSpacePathDist_cosh x (DiscreteGroups.mobiusTranslation b • x)
  rw [parabolic_translation_difference_norm, parabolic_translation_smul,
    quaternionHeight_threePoint] at hc
  change Real.cosh d = 1 + ‖b‖ ^ 2 / (2 * t * t) at hc
  field_simp [ht.ne'] at hc
  have hcosh := Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d by ring] at hcosh
  have hrel := Real.cosh_sq_sub_sinh_sq (d / 2)
  have hs : 0 ≤ Real.sinh (d / 2) := Real.sinh_nonneg_iff.mpr
    (div_nonneg (DiscreteGroups.jorgensen_upperHalfSpacePathDist_nonneg _ _) (by norm_num))
  apply (sq_eq_sq₀ hs (div_nonneg (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * t))).mp
  field_simp [ht.ne']
  linear_combination hc - (2 * t ^ 2) * hcosh - (2 * t ^ 2) * hrel

/-- Translation displacement sublevels are literal horizontal upper half-spaces. -/
theorem parabolicDisplacementSublevel_translation (b : ℂ) (k : ℝ) (hk : 0 < k) :
    parabolicDisplacementSublevel (DiscreteGroups.mobiusTranslation b) k =
      {x : UpperHalfSpace | ‖b‖ / (2 * k) < quaternionHeight x.val} := by
  ext x
  change Real.sinh (Mobius.upperHalfSpacePathDist x (DiscreteGroups.mobiusTranslation b • x) / 2) < k ↔
    ‖b‖ / (2 * k) < quaternionHeight x.val
  rw [parabolic_translation_sinh_displacement,
    div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) x.property),
    div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
  constructor <;> intro h <;> nlinarith

/-- Every nontrivial translation sublevel is a genuine horoball with the correct ideal base infinity. -/
theorem parabolicDisplacementSublevel_translation_isHoroball (b : ℂ) (hb : b ≠ 0)
    (k : ℝ) (hk : 0 < k) : IsHoroballBasedAt (parabolicDisplacementSublevel (DiscreteGroups.mobiusTranslation b) k) ∞ :=
      by
  refine ⟨‖b‖ / (2 * k), by positivity, ?_⟩
  rw [parabolicDisplacementSublevel_translation b k hk, horoballRegion_infty]

/-- The inverse actual Mobius action has the precise height denominator controlling horoball images. -/
theorem horoball_inverse_height (A : Auxiliary.Algebra.SpecialLinear2) (x : UpperHalfSpace) :
    quaternionHeight ((Mobius.mobiusSpecialLinearProjection A)⁻¹ • x).val =
      quaternionHeight x.val /
        (‖-(A 1 0) * quaternionHorizontal x.val + A 0 0‖ ^ 2 +
          ‖A 1 0‖ ^ 2 * quaternionHeight x.val ^ 2) := by
  rw [← map_inv, Mobius.mobiusUpperHalfSpace_smul, Mobius.mobiusPoincareHom_specialLinearProjection]
  change Mobius.poincareHeight ((A⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)
    (quaternionHorizontal x.val) (quaternionHeight x.val) = _
  rw [Mobius.poincareHeight, (A⁻¹).det_coe, norm_one, one_mul]
  simp only [Mobius.poincareDenominator, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, norm_neg]

/-- Actual bijectivity identifies image membership using the inverse height. -/
theorem horoball_image_infty_iff (h : Mobius.complexMobiusGroup) (r : ℝ) (x : UpperHalfSpace) :
    x ∈ (fun y : UpperHalfSpace => h • y) '' horoballRegion ∞ r ↔
      r < quaternionHeight (h⁻¹ • x).val := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change r < quaternionHeight y.val at hy
    change r < quaternionHeight (h⁻¹ • (h • y)).val
    rwa [inv_smul_smul]
  · intro hx
    exact ⟨h⁻¹ • x, hx, smul_inv_smul h x⟩

/-- The actual Euclidean distance to a tangent-ball center splits into horizontal and vertical coordinates. -/
theorem horoball_distance_sq (x : UpperHalfSpace) (w : ℂ) (R : ℝ) :
    dist x.val (quaternionThreePoint w R) ^ 2 =
      ‖quaternionHorizontal x.val - w‖ ^ 2 + (quaternionHeight x.val - R) ^ 2 := by
  have he : x.val - quaternionThreePoint w R =
      quaternionThreePoint (quaternionHorizontal x.val - w) (quaternionHeight x.val - R) := by
    rw [← quaternionThreePoint_coordinates x.val]
    apply Subtype.ext
    apply Quaternion.ext <;> simp [quaternionThreePoint, quaternionHorizontal, quaternionHeight]
  rw [dist_eq_norm, he, Mobius.quaternionThreePoint_norm_sq]

/-- Completing the square identifies the actual tangent-ball radius. -/
theorem horoball_radius_inequality (K : ℝ) (hK : 0 < K) (N t : ℝ) :
    N + (t - 1 / (2 * K)) ^ 2 < (1 / (2 * K)) ^ 2 ↔ K * (N + t ^ 2) < t := by
  have he : K * (N + (t - 1 / (2 * K)) ^ 2 - (1 / (2 * K)) ^ 2) = K * (N + t ^ 2) - t := by
    field_simp [hK.ne']; ring
  calc
    _ ↔ K * (N + (t - 1 / (2 * K)) ^ 2) < K * (1 / (2 * K)) ^ 2 := (mul_lt_mul_iff_right₀ hK).symm
    _ ↔ K * (N + (t - 1 / (2 * K)) ^ 2 - (1 / (2 * K)) ^ 2) < 0 := by rw [mul_sub, sub_lt_zero]
    _ ↔ K * (N + t ^ 2) < t := by rw [he, sub_lt_zero]

/-- The image of every actual infinity-based horoball is a physical horoball at the transformed ideal point. -/
theorem horoballRegion_image_infty (A : Auxiliary.Algebra.SpecialLinear2) (r : ℝ) (hr : 0 < r) :
    ∃ s : ℝ, 0 < s ∧
      (fun x : UpperHalfSpace => Mobius.mobiusSpecialLinearProjection A • x) '' horoballRegion ∞ r =
        horoballRegion ((Mobius.mobiusSpecialLinearProjection A).val ∞) s := by
  have hden (x : UpperHalfSpace) : 0 <
      ‖-(A 1 0) * quaternionHorizontal x.val + A 0 0‖ ^ 2 +
        ‖A 1 0‖ ^ 2 * quaternionHeight x.val ^ 2 := by
    have hd := Mobius.poincareDenominator_pos ((A⁻¹ : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2)
      (by rw [(A⁻¹).det_coe]; exact one_ne_zero) (quaternionHorizontal x.val) (quaternionHeight x.val) x.property
    simpa only [Mobius.poincareDenominator, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, norm_neg] using hd
  by_cases hc : A 1 0 = 0
  · have ha : A 0 0 ≠ 0 := by
      have hd := A.det_coe
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hd
      exact left_ne_zero_of_mul_eq_one hd
    have hi : (Mobius.mobiusSpecialLinearProjection A).val ∞ = ∞ := by
      rw [Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_infty]
      change (if A 1 0 = 0 then ∞ else ((A 0 0 / A 1 0 : ℂ) : Mobius.ExtendedComplex)) = ∞
      simp only [hc, ite_true]
    refine ⟨r * ‖A 0 0‖ ^ 2, by positivity, ?_⟩
    rw [hi]
    ext x
    rw [horoball_image_infty_iff, horoball_inverse_height, lt_div_iff₀ (hden x)]
    change r * (‖-(A 1 0) * quaternionHorizontal x.val + A 0 0‖ ^ 2 +
      ‖A 1 0‖ ^ 2 * quaternionHeight x.val ^ 2) < quaternionHeight x.val ↔
      r * ‖A 0 0‖ ^ 2 < quaternionHeight x.val
    simp only [hc, neg_zero, zero_mul, zero_add, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  · let K := r * ‖A 1 0‖ ^ 2
    have hK : 0 < K := mul_pos hr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hc))
    have hi : (Mobius.mobiusSpecialLinearProjection A).val ∞ = ((A 0 0 / A 1 0 : ℂ) : Mobius.ExtendedComplex) := by
      rw [Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_infty]
      change (if A 1 0 = 0 then ∞ else ((A 0 0 / A 1 0 : ℂ) : Mobius.ExtendedComplex)) = _
      rw [ite_eq_right hc]
    refine ⟨1 / (2 * K), by positivity, ?_⟩
    rw [hi, horoballRegion_coe]
    ext x
    rw [horoball_image_infty_iff, horoball_inverse_height, lt_div_iff₀ (hden x)]
    have hn : ‖-(A 1 0) * quaternionHorizontal x.val + A 0 0‖ ^ 2 =
        ‖A 1 0‖ ^ 2 * ‖quaternionHorizontal x.val - A 0 0 / A 1 0‖ ^ 2 := by
      have he : -(A 1 0) * quaternionHorizontal x.val + A 0 0 =
          -(A 1 0) * (quaternionHorizontal x.val - A 0 0 / A 1 0) := by field_simp; ring
      rw [he, norm_mul, norm_neg, mul_pow]
    change r * (‖-(A 1 0) * quaternionHorizontal x.val + A 0 0‖ ^ 2 +
      ‖A 1 0‖ ^ 2 * quaternionHeight x.val ^ 2) < quaternionHeight x.val ↔
      dist x.val (quaternionThreePoint (A 0 0 / A 1 0) (1 / (2 * K))) < 1 / (2 * K)
    rw [hn, ← sq_lt_sq₀ (dist_nonneg) (by positivity : (0 : ℝ) ≤ 1 / (2 * K)), horoball_distance_sq,
      horoball_radius_inequality K hK]
    dsimp only [K]
    ring_nf

/-- Every actual parabolic is a genuine conjugate of unit translation. -/
theorem parabolic_translation_conjugate (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusParabolic f) :
    ∃ h : Mobius.complexMobiusGroup, f = h * DiscreteGroups.mobiusTranslation 1 * h⁻¹ := by
  obtain ⟨q, hq⟩ := isConj_iff.mp ((Mobius.mobiusBoundaryParabolic_iff_conjugate_translation f hf.1).mp hf)
  have hT : Mobius.mobiusStandardElement 1 = DiscreteGroups.mobiusTranslation 1 :=
    DiscreteGroups.jorgensenSharpnessTranslation_standard.symm
  refine ⟨q⁻¹, ?_⟩
  rw [inv_inv]
  calc
    f = q⁻¹ * (q * f * q⁻¹) * q := by group
    _ = q⁻¹ * DiscreteGroups.mobiusTranslation 1 * q := by rw [hq, hT]

/-- Every parabolic displacement sublevel is an actual physical horoball at its unique fixed ideal point. -/
theorem parabolicDisplacementSublevel_isHoroballBasedAt (f : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f) (k : ℝ) (hk : 0 < k) (w : Mobius.ExtendedComplex) (hw : f.val w = w) :
    IsHoroballBasedAt (parabolicDisplacementSublevel f k) w := by
  obtain ⟨h, hconj⟩ := parabolic_translation_conjugate f hf
  have hfixed : f.val (h.val ∞) = h.val ∞ := by
    change f • (h • (∞ : Mobius.ExtendedComplex)) = h • (∞ : Mobius.ExtendedComplex)
    rw [hconj]
    simp only [mul_smul, inv_smul_smul]
    change h.val ((DiscreteGroups.mobiusTranslation 1).val ∞) = h.val ∞
    rw [DiscreteGroups.mobiusTranslation_infty]
  obtain ⟨a, hfix⟩ := hf.2
  have hw' : h.val ∞ = w := ((hfix _).mp hfixed).trans ((hfix _).mp hw).symm
  have hT : parabolicDisplacementSublevel (DiscreteGroups.mobiusTranslation 1) k = horoballRegion ∞ (1 / (2 * k)) := by
    rw [parabolicDisplacementSublevel_translation 1 k hk, horoballRegion_infty]
    simp only [norm_one]
  have himage := parabolicDisplacementSublevel_image (DiscreteGroups.mobiusTranslation 1) h k
  rw [← hconj, hT] at himage
  obtain ⟨A, hA⟩ := Mobius.mobiusSpecialLinearProjection_surjective h
  obtain ⟨s, hs, he⟩ := horoballRegion_image_infty A (1 / (2 * k)) (by positivity)
  refine ⟨s, hs, ?_⟩
  rw [← himage]
  simpa only [hA, hw'] using he

/-- The canonical set is a physical horoball at the actual parabolic fixed point. -/
theorem canonicalParabolicHoroball_basedAt (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusParabolic f)
    (w : Mobius.ExtendedComplex) (hw : f.val w = w) : IsHoroballBasedAt (canonicalParabolicHoroball f) w :=
  parabolicDisplacementSublevel_isHoroballBasedAt f hf (1 / 2) (by norm_num) w hw

/-- The source's canonical horoball exists as a genuine Euclidean tangent-ball or horizontal-half-space region. -/
theorem canonicalParabolicHoroball_isHoroball (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusParabolic f) :
    IsHoroball (canonicalParabolicHoroball f) := by
  obtain ⟨w, hfix⟩ := hf.2
  exact ⟨w, canonicalParabolicHoroball_basedAt f hf w ((hfix w).mpr rfl)⟩

/-- Canonical parabolic horoballs: actual physical geometry, invariance of the family, and separation for distinct fixed points. -/
theorem canonicalParabolicHoroballs_are_horoballs_invariant_and_disjoint_of_no_commonFixedPoint (H : Subgroup
  Mobius.complexMobiusGroup) (hD : Mobius.IsDiscreteMobiusSubgroup H) :
    (∀ f ∈ H, Mobius.MobiusParabolic f → IsHoroball (canonicalParabolicHoroball f)) ∧
    (∀ h : H, (fun D : Set UpperHalfSpace => (fun x : UpperHalfSpace => h.val • x) '' D) ''
      canonicalParabolicHoroballFamily H = canonicalParabolicHoroballFamily H) ∧
    ∀ f ∈ H, ∀ g ∈ H, Mobius.MobiusParabolic f → Mobius.MobiusParabolic g →
      ¬Mobius.MobiusCommonFixedPoint f g → Disjoint (canonicalParabolicHoroball f) (canonicalParabolicHoroball g) := by
  exact ⟨fun f _ hf => canonicalParabolicHoroball_isHoroball f hf,
    canonicalParabolicHoroballFamily_invariant_and_disjoint_of_no_commonFixedPoint H hD⟩

end LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

