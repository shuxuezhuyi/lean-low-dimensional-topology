module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscGroups
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
/-!
# Invariant discs and the absence of strict loxodromicity

For a non-elementary group, real traces of determinant-one lifts construct
an invariant disc exactly when every element avoids strict loxodromicity.
The common round frontier determines precisely two complementary invariant
discs. Explicit translation groups show why non-elementarity is essential:
independent translations preserve no disc, while one translation preserves
infinitely many distinct half-discs.
-/

@[expose] public section
noncomputable section
open scoped OnePoint ComplexConjugate MatrixGroups UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A complex number whose square is nonnegative real is real. -/
theorem complex_im_eq_zero_of_sq_nonneg_real (z : ℂ)
    (h : ∃ r : ℝ, 0 ≤ r ∧ z ^ 2 = (r : ℂ)) : z.im = 0 := by
  obtain ⟨r, hr, he⟩ := h
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  have hm : z.re * z.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hm with hz | hz
  · rw [hz] at hre
    nlinarith [sq_nonneg z.im]
  · exact hz

/-- Every determinant-one lift of a map that is not strictly loxodromic has real trace. -/
theorem specialLinear_trace_real_of_not_strictlyLoxodromic (A : Auxiliary.Algebra.SpecialLinear2)
    (h : ¬MobiusStrictlyLoxodromic (mobiusSpecialLinearProjection A)) :
    (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0 := by
  by_cases he : mobiusSpecialLinearProjection A = 1
  · exact (specialLinear_elliptic_or_identity_trace A (Or.inl he)).1
  · apply complex_im_eq_zero_of_sq_nonneg_real
    obtain ⟨r, hr, ht⟩ := not_not.mp
      (mt (mobius_strictlyLoxodromic_iff_squaredTrace_not_nonnegative_real (mobiusSpecialLinearProjection A) he).mpr h)
    exact ⟨r, hr, by rwa [mobiusSquaredTrace_specialLinearProjection] at ht⟩

/-- The real-trace restriction is uniform on the full determinant-one preimage subgroup. -/
theorem no_strictlyLoxodromic_lift_trace_real (H : Subgroup complexMobiusGroup)
    (hH : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val) (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A ∈ H) :
    (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0 :=
  specialLinear_trace_real_of_not_strictlyLoxodromic A (hH ⟨_, hA⟩)

/-- Two real traces relative to a noncentral real diagonal matrix force both diagonals real. -/
theorem specialLinear_real_traces_real_diagonal (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0)
    (hR0 : (R 0 0).im = 0) (hR1 : (R 1 1).im = 0)
    (hRn : (R 0 0).re ≠ (R 1 1).re)
    (hA : (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0)
    (hRA : (Matrix.trace ((R * A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)).im = 0) :
    (A 0 0).im = 0 ∧ (A 1 1).im = 0 := by
  simp only [Matrix.trace_fin_two, Complex.add_im] at hA
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, hR01, hR10, zero_mul, add_zero, zero_add,
    Complex.add_im, Complex.mul_im, hR0, hR1, zero_mul, add_zero] at hRA
  have hm : ((R 0 0).re - (R 1 1).re) * (A 0 0).im = 0 := by
    linear_combination hRA - (R 1 1).re * hA
  have hz := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hRn)
  exact ⟨hz, by linarith⟩

/-- A determinant-one matrix with real diagonal has real off-diagonal product. -/
theorem specialLinear_offDiagonal_product_real (A : Auxiliary.Algebra.SpecialLinear2)
    (h0 : (A 0 0).im = 0) (h1 : (A 1 1).im = 0) :
    (A 0 1 * A 1 0).im = 0 := by
  have hd := congrArg Complex.im A.det_coe
  simp only [Matrix.det_fin_two, Complex.sub_im, Complex.mul_im, h0, h1,
    zero_mul, mul_zero, add_zero, Complex.one_im] at hd
  simp only [Complex.mul_im]
  linarith

/-- Products with one real matrix having nonzero off-diagonals recover all four real entries. -/
theorem specialLinear_real_product_diagonal_real_entries (B A : Auxiliary.Algebra.SpecialLinear2)
    (hB : ∀ i j, (B i j).im = 0) (hB01 : B 0 1 ≠ 0) (hB10 : B 1 0 ≠ 0)
    (hA : (A 0 0).im = 0 ∧ (A 1 1).im = 0)
    (hBA : ((B * A) 0 0).im = 0 ∧ ((B * A) 1 1).im = 0) :
    ∀ i j, (A i j).im = 0 := by
  have hb01 : (B 0 1).re ≠ 0 := by
    intro hz
    exact hB01 (Complex.ext (by simpa using hz) (by simpa using hB 0 1))
  have hb10 : (B 1 0).re ≠ 0 := by
    intro hz
    exact hB10 (Complex.ext (by simpa using hz) (by simpa using hB 1 0))
  have h10 : (A 1 0).im = 0 := by
    have he := hBA.1
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.add_im, Complex.mul_im, hB, hA.1, mul_zero, zero_mul, add_zero,
      zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left hb01
  have h01 : (A 0 1).im = 0 := by
    have he := hBA.2
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.add_im, Complex.mul_im, hB, hA.2, mul_zero, zero_mul, add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hb10
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact hA.1 | exact hA.2 | exact h10 | exact h01

/-- The actual determinant-one projection has its exact full-plane matrix action. -/
theorem invariantDisc_specialLinear_action (A : Auxiliary.Algebra.SpecialLinear2) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) =
      fractionalLinear (Matrix.SpecialLinearGroup.toGL A) :=
  mobiusMatrixProjection_coe _

/-- Real determinant-one matrices act on the genuine upper half-plane by its real matrix action. -/
theorem specialLinear_real_upperHalfPlane (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : ∀ i j, (A i j).im = 0) (z : ℍ) :
    ∃ w : ℍ, (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex)
      (z : ℂ) = (w : ℂ) := by
  have hc (i j) : A i j = ((A i j).re : ℂ) :=
    Complex.ext (by simp) (by simpa using hA i j)
  have hd : (A 0 0).re * (A 1 1).re - (A 0 1).re * (A 1 0).re = 1 := by
    have he := congrArg Complex.re A.det_coe
    simpa only [Matrix.det_fin_two, Complex.sub_re, Complex.mul_re, hA,
      zero_mul, sub_zero, Complex.one_re] using he
  let hp : 0 < (A 0 0).re * (A 1 1).re - (A 0 1).re * (A 1 0).re := by
    rw [hd]; exact zero_lt_one
  refine ⟨Hyperbolic.realMobiusMap _ _ _ _ hp z, ?_⟩
  rw [invariantDisc_specialLinear_action, fractionalLinear_coe]
  change (if A 1 0 * z + A 1 1 = 0 then ∞ else
    (((A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1) : ℂ) : ExtendedComplex)) = _
  conv_lhs => rw [hc 1 0, hc 1 1, hc 0 0, hc 0 1,
    ite_eq_right (Hyperbolic.realMobiusMap_den_ne_zero _ _ _ _ hp z)]
  exact congrArg OnePoint.some (Hyperbolic.realMobiusMap_coe _ _ _ _ hp z).symm

/-- A real matrix sends the entire extended real axis to itself, including its pole. -/
theorem specialLinear_real_maps_realAxis (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : ∀ i j, (A i j).im = 0) {z : ExtendedComplex}
    (hz : z ∈ complexRealAxis) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) z ∈ complexRealAxis := by
  rw [invariantDisc_specialLinear_action]
  induction z using OnePoint.rec with
  | infty =>
    rw [fractionalLinear_infty]
    split_ifs
    · exact complexRealAxis_infty
    · rw [complexRealAxis_coe]
      change (A 0 0 / A 1 0).im = 0
      simp [Complex.div_im, hA]
  | coe z =>
    rw [complexRealAxis_coe] at hz
    rw [fractionalLinear_coe]
    split_ifs
    · exact complexRealAxis_infty
    · rw [complexRealAxis_coe]
      change ((A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)).im = 0
      simp [Complex.div_im, Complex.mul_im, hA, hz]

/-- The inverse of a real determinant-one matrix is real. -/
theorem specialLinear_real_inv (A : Auxiliary.Algebra.SpecialLinear2) (hA : ∀ i j, (A i j).im = 0) :
    ∀ i j, (A⁻¹ i j).im = 0 := by
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [hA]

/-- Real determinant-one matrices preserve the actual extended real axis bijectively. -/
theorem specialLinear_real_image_realAxis (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : ∀ i j, (A i j).im = 0) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) '' complexRealAxis =
      complexRealAxis := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact specialLinear_real_maps_realAxis A hA hz
  · intro z hz
    refine ⟨(mobiusSpecialLinearProjection A⁻¹ : Equiv.Perm ExtendedComplex) z,
      specialLinear_real_maps_realAxis A⁻¹ (specialLinear_real_inv A hA) hz, ?_⟩
    simp

/-- The standard open half-disc is an actual complementary component of a generalized circle. -/
def standardComplexHalfDisc : Set ExtendedComplex :=
  connectedComponentIn complexRealAxisᶜ (Complex.I : ExtendedComplex)

theorem standardComplexHalfDisc_isDisc : IsComplexOpenDisc standardComplexHalfDisc := by
  refine ⟨complexRealAxis, complexRealAxis_isGeneralized, Complex.I, ?_, rfl⟩
  simp

/-- Every real determinant-one matrix preserves the same genuine open half-disc. -/
theorem specialLinear_real_preserves_halfDisc (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : ∀ i j, (A i j).im = 0) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc =
      standardComplexHalfDisc := by
  let U : Set ExtendedComplex := OnePoint.some '' {z : ℂ | 0 < z.im}
  have hcv : Convex ℝ {z : ℂ | 0 < z.im} :=
    convex_halfSpace_gt Complex.imLm.isLinear 0
  have hU : IsPreconnected U :=
    hcv.isPreconnected.image OnePoint.some OnePoint.continuous_coe.continuousOn
  have hsub : U ⊆ complexRealAxisᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hreal
    exact (ne_of_gt hz) ((complexRealAxis_coe z).mp hreal)
  have hi : ((Complex.I : ℂ) : ExtendedComplex) ∈ U := ⟨Complex.I, by simp, rfl⟩
  have hD : U ⊆ standardComplexHalfDisc := hU.subset_connectedComponentIn hi hsub
  obtain ⟨w, hw⟩ := specialLinear_real_upperHalfPlane A hA (⟨Complex.I, by simp⟩ : ℍ)
  have hfi : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) Complex.I ∈ U :=
    ⟨(w : ℂ), w.im_pos, hw.symm⟩
  have hcomp := (mobiusBoundaryHomeomorph (mobiusSpecialLinearProjection A)).image_connectedComponentIn
    (hsub hi)
  change (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc =
    connectedComponentIn ((mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) ''
      complexRealAxisᶜ) ((mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) Complex.I) at hcomp
  rw [(mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex).image_compl complexRealAxis,
    specialLinear_real_image_realAxis A hA] at hcomp
  exact hcomp.trans (connectedComponentIn_eq (hD hfi)).symm

/-- A subgroup whose lifts all have real entries has a common geometric invariant disc. -/
theorem hasInvariantComplexDisc_of_real_lifts (H : Subgroup complexMobiusGroup)
    (hH : ∀ A : Auxiliary.Algebra.SpecialLinear2, mobiusSpecialLinearProjection A ∈ H →
      ∀ i j, (A i j).im = 0) : HasInvariantComplexDisc H := by
  refine ⟨standardComplexHalfDisc, standardComplexHalfDisc_isDisc, ?_⟩
  intro f
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective f.val
  rw [← hA]
  exact specialLinear_real_preserves_halfDisc A (hH A (hA.symm ▸ f.property))

/-- Finite orbits are invariant under actual subgroup conjugation. -/
theorem invariantDisc_finiteOrbit_conjugation {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (q : G) :
    DiscreteGroups.Action.HasFiniteOrbit (H.map (MulAut.conj q).toMonoidHom) X ↔
      DiscreteGroups.Action.HasFiniteOrbit H X := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨q⁻¹ • x, (hx.image (fun y => q⁻¹ • y)).subset ?_⟩
    rintro y ⟨h, rfl⟩
    refine ⟨(q * h.val * q⁻¹) • x, ?_, ?_⟩
    · exact ⟨⟨q * h.val * q⁻¹, ⟨h.val, h.property, rfl⟩⟩, rfl⟩
    · simp only [mul_smul, inv_smul_smul]
      rfl
  · rintro ⟨x, hx⟩
    refine ⟨q • x, (hx.image (fun y => q • y)).subset ?_⟩
    rintro y ⟨h, rfl⟩
    obtain ⟨g, hg, hgh⟩ := h.property
    refine ⟨g • x, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    change q • g • x = h.val • q • x
    rw [← hgh]
    change q • g • x = (q * g * q⁻¹) • q • x
    simp only [mul_smul, inv_smul_smul]

/-- Non-elementarity is unchanged by an actual Mobius conjugation. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary.conjugation {H : Subgroup
    complexMobiusGroup}
    (hH : DiscreteGroups.IsNonElementary H) (q : complexMobiusGroup) :
    DiscreteGroups.IsNonElementary (H.map (MulAut.conj q).toMonoidHom) :=
  fun hc => hH ((invariantDisc_finiteOrbit_conjugation H q).mp hc)

/-- A non-elementary group cannot fix any actual boundary point. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary.exists_move_boundary {H : Subgroup
    complexMobiusGroup}
    (hH : DiscreteGroups.IsNonElementary H) (z : ExtendedComplex) :
    ∃ f : H, (f.val : Equiv.Perm ExtendedComplex) z ≠ z := by
  by_contra! hc
  exact hH (DiscreteGroups.isElementary_of_boundary_fixed H z hc)

/-- A non-elementary group has a nonidentity element that is not elliptic. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary.exists_not_elliptic {H : Subgroup
    complexMobiusGroup}
    (hH : DiscreteGroups.IsNonElementary H) : ∃ f ∈ H, f ≠ 1 ∧ ¬MobiusElliptic f := by
  by_contra! he
  obtain ⟨q, hq⟩ := (all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).mp he
  exact hH (DiscreteGroups.isElementary_of_interior_fixed H q (fun f => hq f.val f.property))

/-- Absence of strictly loxodromic maps survives conjugation of the entire subgroup. -/
theorem noStrictlyLoxodromic_conjugation (H : Subgroup complexMobiusGroup)
    (hH : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val) (q : complexMobiusGroup) :
    ∀ f : H.map (MulAut.conj q).toMonoidHom, ¬MobiusStrictlyLoxodromic f.val := by
  intro f
  obtain ⟨g, hg, he⟩ := f.property
  rw [← he]
  change ¬MobiusStrictlyLoxodromic (q * g * q⁻¹)
  exact fun hf => hH ⟨g, hg⟩ ((mobiusStrictlyLoxodromic_isConj
    (isConj_iff.mpr ⟨q, rfl⟩)).mpr hf)

/-- Common invariant discs transport back from any actual conjugate subgroup. -/
theorem HasInvariantComplexDisc.of_conjugation (H : Subgroup complexMobiusGroup)
    (q : complexMobiusGroup)
    (h : HasInvariantComplexDisc (H.map (MulAut.conj q).toMonoidHom)) :
    HasInvariantComplexDisc H := by
  obtain ⟨D, hD, hp⟩ := h
  refine ⟨(q⁻¹ : Equiv.Perm ExtendedComplex) '' D, hD.image q⁻¹, ?_⟩
  intro f
  have he := hp ⟨q * f.val * q⁻¹, ⟨f.val, f.property, rfl⟩⟩
  change (q * f.val * q⁻¹ : Equiv.Perm ExtendedComplex) '' D = D at he
  have hi := congrArg (fun S => (q⁻¹ : Equiv.Perm ExtendedComplex) '' S) he
  rw [Set.image_image] at hi ⊢
  change (fun z => (q : Equiv.Perm ExtendedComplex).symm
    ((q : Equiv.Perm ExtendedComplex) ((f.val : Equiv.Perm ExtendedComplex)
      ((q : Equiv.Perm ExtendedComplex).symm z)))) '' D = _ at hi
  simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using hi

/-- A real diagonal hyperbolic element and one real transverse element force a common disc. -/
theorem hasInvariantComplexDisc_of_real_trace_generators (H : Subgroup complexMobiusGroup)
    (hH : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val)
    (R B : Auxiliary.Algebra.SpecialLinear2) (hR : mobiusSpecialLinearProjection R ∈ H)
    (hB : mobiusSpecialLinearProjection B ∈ H)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0)
    (hR0 : (R 0 0).im = 0) (hR1 : (R 1 1).im = 0)
    (hRn : (R 0 0).re ≠ (R 1 1).re)
    (hBre : ∀ i j, (B i j).im = 0) (hB01 : B 0 1 ≠ 0) (hB10 : B 1 0 ≠ 0) :
    HasInvariantComplexDisc H := by
  have hdiag (A : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A ∈ H) :
      (A 0 0).im = 0 ∧ (A 1 1).im = 0 := by
    apply specialLinear_real_traces_real_diagonal R A hR01 hR10 hR0 hR1 hRn
    · exact no_strictlyLoxodromic_lift_trace_real H hH A hA
    · exact no_strictlyLoxodromic_lift_trace_real H hH (R * A) (by
        rw [map_mul]; exact H.mul_mem hR hA)
  apply hasInvariantComplexDisc_of_real_lifts H
  intro A hA
  exact specialLinear_real_product_diagonal_real_entries B A hBre hB01 hB10
    (hdiag A hA) (hdiag (B * A) (by rw [map_mul]; exact H.mul_mem hB hA))

/-- Two distinct boundary points cannot together force every non-elementary element to fix one. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary.exists_move_two {H : Subgroup
    complexMobiusGroup}
    (hH : DiscreteGroups.IsNonElementary H) (a b : ExtendedComplex) :
    ∃ f : H, (f.val : Equiv.Perm ExtendedComplex) a ≠ a ∧
      (f.val : Equiv.Perm ExtendedComplex) b ≠ b := by
  obtain ⟨f, hfa⟩ := hH.exists_move_boundary a
  by_cases hfb : (f.val : Equiv.Perm ExtendedComplex) b = b
  · obtain ⟨g, hgb⟩ := hH.exists_move_boundary b
    by_cases hga : (g.val : Equiv.Perm ExtendedComplex) a = a
    · refine ⟨f * g, ?_, ?_⟩
      · change (f.val : Equiv.Perm ExtendedComplex) ((g.val : Equiv.Perm ExtendedComplex) a) ≠ a
        rwa [hga]
      · change (f.val : Equiv.Perm ExtendedComplex) ((g.val : Equiv.Perm ExtendedComplex) b) ≠ b
        intro he
        exact hgb ((f.val : Equiv.Perm ExtendedComplex).injective (he.trans hfb.symm))
    · exact ⟨g, hga, hgb⟩
  · exact ⟨f, hfa, hfb⟩

/-- A non-elementary group supplies a determinant-one matrix with both off-diagonals nonzero. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary.exists_transverse_lift {H : Subgroup
    complexMobiusGroup}
    (hH : DiscreteGroups.IsNonElementary H) : ∃ B : Auxiliary.Algebra.SpecialLinear2,
    mobiusSpecialLinearProjection B ∈ H ∧ B 0 1 ≠ 0 ∧ B 1 0 ≠ 0 := by
  obtain ⟨f, h0, hi⟩ := hH.exists_move_two (0 : ℂ) ∞
  obtain ⟨B, hB⟩ := mobiusSpecialLinearProjection_surjective f.val
  refine ⟨B, hB.symm ▸ f.property, ?_, ?_⟩
  · intro hb
    have hd : B 1 1 ≠ 0 := by
      intro hd
      have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
        simpa only [Matrix.det_fin_two] using B.det_coe
      simp only [hb, hd, mul_zero, zero_mul, sub_self] at hdet
      exact zero_ne_one hdet
    apply h0
    rw [← hB, invariantDisc_specialLinear_action, fractionalLinear_coe]
    change (if B 1 0 * 0 + B 1 1 = 0 then ∞ else
      (((B 0 0 * 0 + B 0 1) / (B 1 0 * 0 + B 1 1) : ℂ) : ExtendedComplex)) = _
    simp [hd, hb]
  · intro hc
    apply hi
    rw [← hB, invariantDisc_specialLinear_action, fractionalLinear_infty]
    change (if B 1 0 = 0 then ∞ else ((B 0 0 / B 1 0 : ℂ) : ExtendedComplex)) = ∞
    simp [hc]

/-- Hyperbolic maps admit positive real standard forms in the actual group. -/
theorem mobiusHyperbolic_conjugate_positive_standard {f : complexMobiusGroup}
    (hf : MobiusHyperbolic f) : ∃ q : complexMobiusGroup, ∃ k : ℂˣ,
    (k : ℂ).im = 0 ∧ 0 < (k : ℂ).re ∧ ‖(k : ℂ)‖ ≠ 1 ∧
      q * f * q⁻¹ = mobiusStandardElement k := by
  obtain ⟨r, hr, ht⟩ := (mobius_hyperbolic_iff_squaredTrace_real_gt_four f hf.1.1).mp hf
  obtain ⟨k, hki, hkp, hkn, hk⟩ := exists_positive_standard_squaredTrace r hr
  have hc := (mobius_isConj_iff_squaredTrace_eq f _ hf.1.1 (mobiusStandardElement_ne_one k)).mpr
    (ht.trans hk.symm)
  obtain ⟨q, hq⟩ := isConj_iff.mp hc
  exact ⟨q, k, hki, hkp, hkn, hq⟩

/-- Positive real nonunit standard maps have noncentral real diagonal determinant-one lifts. -/
theorem positive_standard_real_diagonal_lift (k : ℂˣ) (hki : (k : ℂ).im = 0)
    (hkp : 0 < (k : ℂ).re) (hkn : ‖(k : ℂ)‖ ≠ 1) :
    ∃ R : Auxiliary.Algebra.SpecialLinear2, mobiusSpecialLinearProjection R = mobiusStandardElement k ∧
      R 0 1 = 0 ∧ R 1 0 = 0 ∧ (R 0 0).im = 0 ∧ (R 1 1).im = 0 ∧
      (R 0 0).re ≠ (R 1 1).re := by
  obtain ⟨R, hR, u, ha, hb, hc, hd⟩ := Mobius.Classification.specialStandard_lift k
  have hp : mobiusSpecialLinearProjection R = mobiusStandardElement k := by
    apply complexMobiusEquivFractionalLinear.injective
    rw [mobiusSpecialLinearProjection_equiv, mobiusStandardElement_equiv]
    exact hR
  have hkn1 : (k : ℂ) ≠ 1 := by intro he; exact hkn (by rw [he]; simp)
  have ht := specialLinear_trace_real_of_not_strictlyLoxodromic R (by
    rw [hp]
    exact fun hs => hs.2 (mobiusStandardElement_positive_isHyperbolic k hki hkp hkn))
  have hui : (u : ℂ).im = 0 := by
    simp only [Matrix.trace_fin_two, ha, hd, Complex.add_im, Complex.mul_im, hki,
      mul_zero, zero_add] at ht
    nlinarith
  have hur : (u : ℂ).re ≠ 0 := by
    intro hz
    exact u.ne_zero (Complex.ext (by simpa using hz) (by simpa using hui))
  refine ⟨R, hp, by simp [hb, hkn1], hc, ?_, ?_, ?_⟩
  · simp [ha, Complex.mul_im, hki, hui]
  · simpa [hd] using hui
  · rw [ha, hd, Complex.mul_re, hui, hki, mul_zero, sub_zero]
    intro he
    have hk1 : (k : ℂ).re = 1 := by
      have hz : (u : ℂ).re * ((k : ℂ).re - 1) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hur)
    exact hkn1 (Complex.ext (by simpa using hk1) (by simpa using hki))

/-- Change complex coordinates by a nonzero scalar without changing determinant. -/
def invariantDiscScaleLift (v : ℂˣ) (A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.SpecialLinear2 :=
  ⟨!![A 0 0, (v : ℂ) * A 0 1; (v : ℂ)⁻¹ * A 1 0, A 1 1], by
    rw [Matrix.det_fin_two]
    change A 0 0 * A 1 1 - ((v : ℂ) * A 0 1) * ((v : ℂ)⁻¹ * A 1 0) = 1
    have he : ((v : ℂ) * A 0 1) * ((v : ℂ)⁻¹ * A 1 0) = A 0 1 * A 1 0 := by
      calc
        _ = ((v : ℂ) * (v : ℂ)⁻¹) * (A 0 1 * A 1 0) := by ring
        _ = _ := by simp
    rw [he]
    simpa only [Matrix.det_fin_two] using A.det_coe⟩

/-- Inverse of the actual diagonal coordinate matrix. -/
theorem invariantDisc_affineMatrix_inv (v : ℂˣ) :
    (Mobius.Classification.affineMatrix v 0)⁻¹ = Mobius.Classification.affineMatrix v⁻¹ 0 := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mobius.Classification.affineMatrix, coefficientMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The scaled lift is exactly conjugation, including the pole and infinity. -/
theorem invariantDiscScaleLift_projection (v : ℂˣ) (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusSpecialLinearProjection (invariantDiscScaleLift v A) =
      mobiusMatrixProjection (Mobius.Classification.affineMatrix v 0) *
      mobiusSpecialLinearProjection A *
      (mobiusMatrixProjection (Mobius.Classification.affineMatrix v 0))⁻¹ := by
  change mobiusMatrixProjection (Matrix.SpecialLinearGroup.toGL (invariantDiscScaleLift v A)) =
    mobiusMatrixProjection (Mobius.Classification.affineMatrix v 0) *
      mobiusMatrixProjection (Matrix.SpecialLinearGroup.toGL A) *
      (mobiusMatrixProjection (Mobius.Classification.affineMatrix v 0))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg mobiusMatrixProjection
  rw [invariantDisc_affineMatrix_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invariantDiscScaleLift, Mobius.Classification.affineMatrix, coefficientMatrix,
      Matrix.SpecialLinearGroup.toGL, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] <;> field_simp

/-- Noncentral real diagonal elements force a common invariant disc in a non-elementary group. -/
theorem hasInvariantComplexDisc_of_real_diagonal_element (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) (hns : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val)
    (R : Auxiliary.Algebra.SpecialLinear2) (hR : mobiusSpecialLinearProjection R ∈ H)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0)
    (hR0 : (R 0 0).im = 0) (hR1 : (R 1 1).im = 0)
    (hRn : (R 0 0).re ≠ (R 1 1).re) : HasInvariantComplexDisc H := by
  have hdiag (A : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A ∈ H) :
      (A 0 0).im = 0 ∧ (A 1 1).im = 0 := by
    apply specialLinear_real_traces_real_diagonal R A hR01 hR10 hR0 hR1 hRn
    · exact no_strictlyLoxodromic_lift_trace_real H hns A hA
    · exact no_strictlyLoxodromic_lift_trace_real H hns (R * A) (by
        rw [map_mul]; exact H.mul_mem hR hA)
  obtain ⟨B, hB, hb, hc⟩ := hH.exists_transverse_lift
  let v : ℂˣ := Units.mk0 (B 1 0) hc
  let q := mobiusMatrixProjection (Mobius.Classification.affineMatrix v 0)
  let K := H.map (MulAut.conj q).toMonoidHom
  have hm (A : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A ∈ H) :
      mobiusSpecialLinearProjection (invariantDiscScaleLift v A) ∈ K := by
    rw [invariantDiscScaleLift_projection]
    exact ⟨mobiusSpecialLinearProjection A, hA, rfl⟩
  have hr : invariantDiscScaleLift v R = R := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [invariantDiscScaleLift, hR01, hR10]
  have hBdiag := hdiag B hB
  have hprod := specialLinear_offDiagonal_product_real B hBdiag.1 hBdiag.2
  have hnew : ∀ i j, ((invariantDiscScaleLift v B) i j).im = 0 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hBdiag.1
    · change (B 1 0 * B 0 1).im = 0
      rwa [mul_comm]
    · change ((B 1 0)⁻¹ * B 1 0).im = 0
      simp [hc]
    · exact hBdiag.2
  apply Mobius.HasInvariantComplexDisc.of_conjugation H q
  apply hasInvariantComplexDisc_of_real_trace_generators K
    (noStrictlyLoxodromic_conjugation H hns q) R (invariantDiscScaleLift v B)
    (hr ▸ hm R hR) (hm B hB) hR01 hR10 hR0 hR1 hRn hnew
  · change (B 1 0) * B 0 1 ≠ 0
    exact mul_ne_zero hc hb
  · change ((B 1 0)⁻¹ * B 1 0) ≠ 0
    simp [hc]

/-- Once a hyperbolic element exists, no strictly loxodromic elements force a common disc. -/
theorem hasInvariantComplexDisc_of_hyperbolic_element (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) (hns : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val)
    {f : complexMobiusGroup} (hf : f ∈ H) (hfh : MobiusHyperbolic f) :
    HasInvariantComplexDisc H := by
  obtain ⟨q, k, hki, hkp, hkn, hq⟩ := mobiusHyperbolic_conjugate_positive_standard hfh
  let K := H.map (MulAut.conj q).toMonoidHom
  obtain ⟨R, hR, hR01, hR10, hR0, hR1, hRn⟩ :=
    positive_standard_real_diagonal_lift k hki hkp hkn
  have hmem : mobiusSpecialLinearProjection R ∈ K := by
    rw [hR, ← hq]
    exact ⟨f, hf, rfl⟩
  exact Mobius.HasInvariantComplexDisc.of_conjugation H q
    (hasInvariantComplexDisc_of_real_diagonal_element K (hH.conjugation q)
      (noStrictlyLoxodromic_conjugation H hns q) R hmem hR01 hR10 hR0 hR1 hRn)

/-- A real arithmetic progression with nonzero step eventually has squared modulus above four. -/
theorem invariantDisc_exists_nat_trace_gt_four (a c : ℝ) (hc : c ≠ 0) :
    ∃ n : ℕ, 4 < (a + n * c) ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((|a| + 3) / |c|)
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hn' : |a| + 3 < (n : ℝ) * |c| := (div_lt_iff₀ hcpos).mp hn
  have hbound : (n : ℝ) * |c| ≤ |a + n * c| + |a| := by
    have he := abs_add_le (a + n * c) (-a)
    have hi : a + (n : ℝ) * c + -a = (n : ℝ) * c := by ring
    rw [hi, abs_mul, abs_of_nonneg (Nat.cast_nonneg n), abs_neg] at he
    exact he
  have hz : 2 < |a + (n : ℝ) * c| := by linarith
  refine ⟨n, ?_⟩
  nlinarith [sq_abs (a + (n : ℝ) * c)]

/-- Determinant-one representative of unit translation. -/
def invariantDiscTranslationLift : Auxiliary.Algebra.SpecialLinear2 :=
  ⟨!![1, 1; 0, 1], by simp⟩

theorem invariantDiscTranslationLift_projection :
    mobiusSpecialLinearProjection invariantDiscTranslationLift = mobiusStandardElement 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  rw [invariantDisc_specialLinear_action]
  induction z using OnePoint.rec with
  | infty =>
    rw [fractionalLinear_infty, mobiusStandardElement_infty]
    simp [invariantDiscTranslationLift, Matrix.SpecialLinearGroup.toGL]
  | coe z =>
    rw [fractionalLinear_coe, mobiusStandardElement_coe]
    change (if (0 : ℂ) * z + 1 = 0 then ∞ else
      (((1 * z + 1) / (0 * z + 1) : ℂ) : ExtendedComplex)) = _
    simp

/-- The exact matrix of every nonnegative integral translation power. -/
theorem invariantDiscTranslationLift_pow (n : ℕ) :
    ((invariantDiscTranslationLift ^ n : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) =
      !![1, (n : ℂ); 0, 1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [invariantDiscTranslationLift, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_add,
        Nat.cast_one, add_comm]

/-- Translation powers expose the lower-left coefficient in the ordinary trace. -/
theorem invariantDiscTranslationLift_pow_trace (n : ℕ) (A : Auxiliary.Algebra.SpecialLinear2) :
    Matrix.trace ((invariantDiscTranslationLift ^ n * A : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2) =
      Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) + (n : ℂ) * A 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, invariantDiscTranslationLift_pow]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, zero_mul, zero_add]
  ring

/-- A translation in a non-elementary real-trace group produces a hyperbolic element. -/
theorem invariantDisc_exists_hyperbolic_of_translation (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) (hns : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val)
    (hT : mobiusStandardElement 1 ∈ H) :
    ∃ f ∈ H, MobiusHyperbolic f := by
  obtain ⟨B, hB, _, hc⟩ := hH.exists_transverse_lift
  have hBT : mobiusSpecialLinearProjection (invariantDiscTranslationLift * B) ∈ H := by
    rw [map_mul, invariantDiscTranslationLift_projection]
    exact H.mul_mem hT hB
  have htr := no_strictlyLoxodromic_lift_trace_real H hns B hB
  have htr1 := no_strictlyLoxodromic_lift_trace_real H hns
    (invariantDiscTranslationLift * B) hBT
  have htraceone : Matrix.trace ((invariantDiscTranslationLift * B : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2) = Matrix.trace (B : Auxiliary.Algebra.ComplexMatrix2) + B 1 0 := by
    simpa using invariantDiscTranslationLift_pow_trace 1 B
  rw [htraceone, Complex.add_im, htr, zero_add] at htr1
  have hcr : (B 1 0).re ≠ 0 := by
    intro he
    exact hc (Complex.ext (by simpa using he) (by simpa using htr1))
  obtain ⟨n, hn⟩ := invariantDisc_exists_nat_trace_gt_four
    (Matrix.trace (B : Auxiliary.Algebra.ComplexMatrix2)).re (B 1 0).re hcr
  let A := invariantDiscTranslationLift ^ n * B
  have hA : mobiusSpecialLinearProjection A ∈ H := by
    change mobiusSpecialLinearProjection (invariantDiscTranslationLift ^ n * B) ∈ H
    rw [map_mul, map_pow, invariantDiscTranslationLift_projection]
    exact H.mul_mem (H.pow_mem hT n) hB
  have hta : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) =
      (((Matrix.trace (B : Auxiliary.Algebra.ComplexMatrix2)).re + (n : ℝ) * (B 1 0).re : ℝ) : ℂ) := by
    rw [show (A : Auxiliary.Algebra.ComplexMatrix2) =
      ((invariantDiscTranslationLift ^ n * B : Auxiliary.Algebra.SpecialLinear2) :
        Auxiliary.Algebra.ComplexMatrix2) from rfl,
      invariantDiscTranslationLift_pow_trace]
    apply Complex.ext
    · simp
    · simp [Complex.mul_im, htr, htr1]
  have hsq : mobiusSquaredTrace (mobiusSpecialLinearProjection A) =
      ((((Matrix.trace (B : Auxiliary.Algebra.ComplexMatrix2)).re + (n : ℝ) * (B 1 0).re) ^ 2 : ℝ) : ℂ) := by
    rw [mobiusSquaredTrace_specialLinearProjection, hta, Complex.ofReal_pow]
  have hne : mobiusSpecialLinearProjection A ≠ 1 := by
    intro he
    have hone : mobiusSquaredTrace (1 : complexMobiusGroup) = 4 := by
      have hh := mobiusSquaredTrace_specialLinearProjection (1 : Auxiliary.Algebra.SpecialLinear2)
      norm_num [Matrix.trace_fin_two] at hh
      exact hh
    have hi := congrArg Complex.re hsq
    rw [he, hone, Complex.ofReal_re] at hi
    norm_num at hi
    linarith
  exact ⟨mobiusSpecialLinearProjection A, hA,
    (mobius_hyperbolic_iff_squaredTrace_real_gt_four _ hne).mpr ⟨_, hn, hsq⟩⟩

/-- Non-elementarity and the absence of strictly loxodromic maps supply a hyperbolic map. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary.exists_hyperbolic_of_noStrictlyLoxodromic
    {H : Subgroup complexMobiusGroup} (hH : DiscreteGroups.IsNonElementary H)
    (hns : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val) :
    ∃ f ∈ H, MobiusHyperbolic f := by
  obtain ⟨f, hf, hne, hneE⟩ := hH.exists_not_elliptic
  rcases mobius_nonidentity_type_trichotomy f hne with hp | hl | he
  · obtain ⟨q, hq⟩ := isConj_iff.mp
      ((mobiusBoundaryParabolic_iff_conjugate_translation f hne).mp hp)
    let K := H.map (MulAut.conj q).toMonoidHom
    have hT : mobiusStandardElement 1 ∈ K := ⟨f, hf, hq⟩
    obtain ⟨g, hg, hgh⟩ := invariantDisc_exists_hyperbolic_of_translation K
      (hH.conjugation q) (noStrictlyLoxodromic_conjugation H hns q) hT
    obtain ⟨a, ha, heq⟩ := hg
    refine ⟨a, ha, ?_⟩
    apply (mobiusHyperbolic_conjugation a q).mp
    change q * a * q⁻¹ = g at heq
    rwa [heq]
  · by_contra hn
    exact hns ⟨f, hf⟩ ⟨hl, fun hh => hn ⟨f, hf, hh⟩⟩
  · exact (hneE he).elim

/-- The existence equivalence, for the actual non-elementary group. -/
theorem invariant_disc_iff_no_strictlyLoxodromic (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) :
    HasInvariantComplexDisc H ↔ ∀ f : H, ¬MobiusStrictlyLoxodromic f.val := by
  constructor
  · exact Mobius.HasInvariantComplexDisc.no_strictly_loxodromic H
  · intro hns
    obtain ⟨f, hf, hh⟩ := hH.exists_hyperbolic_of_noStrictlyLoxodromic hns
    exact hasInvariantComplexDisc_of_hyperbolic_element H hH hns hf hh

/-- Three distinct genuine points determine a generalized circle. -/
theorem complexGeneralizedCircle_eq_of_triple {S T : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) (hT : IsComplexGeneralizedCircle T)
    {a b c : ExtendedComplex} (hd : TripleDistinct a b c)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T) : S = T := by
  obtain ⟨q, h0, h1, hi⟩ := mobius_normalize_triple a b c hd
  have hs : (q : Equiv.Perm ExtendedComplex) '' S = complexRealAxis :=
    complexCircle_through_zero_one_infty (hS.image q.property.1)
      ⟨a, haS, h0⟩ ⟨b, hbS, h1⟩ ⟨c, hcS, hi⟩
  have ht : (q : Equiv.Perm ExtendedComplex) '' T = complexRealAxis :=
    complexCircle_through_zero_one_infty (hT.image q.property.1)
      ⟨a, haT, h0⟩ ⟨b, hbT, h1⟩ ⟨c, hcT, hi⟩
  exact (Set.image_injective.mpr (q : Equiv.Perm ExtendedComplex).injective) (hs.trans ht.symm)

/-- All actual boundary fixed points of hyperbolic elements in the subgroup. -/
def hyperbolicBoundaryVertices (H : Subgroup complexMobiusGroup) : Set ExtendedComplex :=
  {z | ∃ f ∈ H, MobiusHyperbolic f ∧ (f : Equiv.Perm ExtendedComplex) z = z}

/-- The hyperbolic vertex set is stable under the entire true subgroup action. -/
theorem hyperbolicBoundaryVertices_smul (H : Subgroup complexMobiusGroup) (g : H)
    {z : ExtendedComplex} (hz : z ∈ hyperbolicBoundaryVertices H) :
    g • z ∈ hyperbolicBoundaryVertices H := by
  obtain ⟨f, hf, hh, hz⟩ := hz
  refine ⟨g.val * f * g.val⁻¹, H.mul_mem (H.mul_mem g.property hf) (H.inv_mem g.property),
    (mobiusHyperbolic_conjugation f g.val).mpr hh, ?_⟩
  exact mobius_disc_conjugate_fixed f g.val hz

/-- Every invariant disc contains the entire hyperbolic vertex set in its actual frontier. -/
theorem hyperbolicBoundaryVertices_subset_frontier (H : Subgroup complexMobiusGroup)
    {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hp : ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' D = D) :
    hyperbolicBoundaryVertices H ⊆ frontier D := by
  rintro z ⟨f, hf, hh, hz⟩
  exact mobiusHyperbolic_fixed_mem_disc_frontier f hh hD (hp ⟨f, hf⟩) hz

/-- A non-elementary subgroup admitting an invariant disc has infinitely many hyperbolic vertices. -/
theorem hyperbolicBoundaryVertices_infinite (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) (hD : HasInvariantComplexDisc H) :
    (hyperbolicBoundaryVertices H).Infinite := by
  obtain ⟨f, hf, hh⟩ := hH.exists_hyperbolic_of_noStrictlyLoxodromic
    (Mobius.HasInvariantComplexDisc.no_strictly_loxodromic H hD)
  obtain ⟨z, hz⟩ := DiscreteGroups.mobius_nonidentity_boundary_fixed_exists f hh.1.1
  have hm : z ∈ hyperbolicBoundaryVertices H := ⟨f, hf, hh, hz⟩
  intro hs
  apply hH
  apply (DiscreteGroups.isElementary_iff_boundary_or_interior H).mpr
  left
  refine ⟨z, hs.subset ?_⟩
  rintro w ⟨g, rfl⟩
  exact hyperbolicBoundaryVertices_smul H g hm

/-- Two discs invariant under the same non-elementary group have the same geometric boundary. -/
theorem invariantComplexDiscs_frontier_eq (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) {D E : Set ExtendedComplex}
    (hD : IsComplexOpenDisc D) (hE : IsComplexOpenDisc E)
    (hpD : ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' D = D)
    (hpE : ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' E = E) : frontier D = frontier E := by
  have hs := hyperbolicBoundaryVertices_infinite H hH ⟨D, hD, hpD⟩
  obtain ⟨a, ha⟩ := hs.nonempty
  obtain ⟨b, hb, hba⟩ := (hs.sdiff (Set.finite_singleton a)).nonempty
  obtain ⟨c, hc, hcab⟩ := (hs.sdiff ((Set.finite_singleton b).insert a)).nonempty
  have hab : a ≠ b := by simpa using Ne.symm hba
  have hcne : c ≠ a ∧ c ≠ b := by simpa using hcab
  have hac : a ≠ c := Ne.symm hcne.1
  have hbc : b ≠ c := by
    exact Ne.symm (fun he => hcab (by simp [he]))
  apply complexGeneralizedCircle_eq_of_triple (complexDisc_frontier_isGeneralized hD)
    (complexDisc_frontier_isGeneralized hE) ⟨hab, hac, hbc⟩
  · exact hyperbolicBoundaryVertices_subset_frontier H hD hpD ha
  · exact hyperbolicBoundaryVertices_subset_frontier H hD hpD hb
  · exact hyperbolicBoundaryVertices_subset_frontier H hD hpD hc
  · exact hyperbolicBoundaryVertices_subset_frontier H hE hpE ha
  · exact hyperbolicBoundaryVertices_subset_frontier H hE hpE hb
  · exact hyperbolicBoundaryVertices_subset_frontier H hE hpE hc

/-- An open preconnected set is a full component of the complement of its frontier. -/
theorem invariantDisc_component_of_open_preconnected {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : IsOpen D) (hc : IsPreconnected D) {z : X} (hz : z ∈ D) :
    connectedComponentIn (frontier D)ᶜ z = D := by
  have hunion : (frontier D)ᶜ = D ∪ interior Dᶜ := by
    rw [compl_frontier_eq_union_interior, hD.interior_eq]
  have hsub : D ⊆ (frontier D)ᶜ := by rw [hunion]; exact Set.subset_union_left
  have hdis : Disjoint D (interior Dᶜ) := by
    exact Set.disjoint_left.mpr (fun x hx hi => interior_subset hi hx)
  apply Set.Subset.antisymm
  · apply IsPreconnected.subset_left_of_subset_union hD isOpen_interior hdis
    · rw [← hunion]
      exact connectedComponentIn_subset _ _
    · exact ⟨z, mem_connectedComponentIn (hsub hz), hz⟩
    · exact isPreconnected_connectedComponentIn
  · exact hc.subset_connectedComponentIn hz hsub

/-- Any genuine disc with the unit circle as frontier is one of its two genuine sides. -/
theorem complexDisc_eq_disc_or_exterior_of_unit_frontier {E : Set ExtendedComplex}
    (hE : IsComplexOpenDisc E) (hf : frontier E = complexCircle 0 1) :
    E = Hyperbolic.extendedUnitDisc ∨ E = extendedUnitDiscExterior := by
  obtain ⟨z, hz⟩ := hE.isConnected.nonempty
  have he := invariantDisc_component_of_open_preconnected hE.isOpen hE.isConnected.isPreconnected hz
  have hm : E ∈ {S : Set ExtendedComplex | ∃ z ∈ (complexCircle 0 1)ᶜ,
      connectedComponentIn (complexCircle 0 1)ᶜ z = S} := by
    refine ⟨z, ?_, by rwa [hf] at he⟩
    rw [← hf, compl_frontier_eq_union_interior, hE.isOpen.interior_eq]
    exact Or.inl hz
  rw [unitCircle_complement_components] at hm
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm

/-- The closure of the actual unit disc is exactly its actual closed disc. -/
theorem invariantDisc_closure_unitDisc : closure Hyperbolic.extendedUnitDisc = Hyperbolic.extendedClosedUnitDisc := by
  rw [closure_eq_self_union_frontier, frontier_extendedUnitDisc_eq_circle]
  ext z
  induction z using OnePoint.rec with
  | infty => simp [infty_not_mem_extendedUnitDisc, Hyperbolic.extendedClosedUnitDisc]
  | coe z =>
    simp only [Set.mem_union, Hyperbolic.coe_mem_extendedUnitDisc, complexCircle_coe, sub_zero,
      Hyperbolic.coe_mem_extendedClosedUnitDisc]
    constructor
    · rintro (h | h)
      · exact h.le
      · exact h.le
    · exact lt_or_eq_of_le

/-- Actual disc normalizations also identify the actual exterior, the complement of the closure. -/
theorem complexDisc_normalize_exterior (q : complexMobiusGroup) {D : Set ExtendedComplex}
    (hq : (q : Equiv.Perm ExtendedComplex) '' D = Hyperbolic.extendedUnitDisc) :
    (q : Equiv.Perm ExtendedComplex) '' (closure D)ᶜ = extendedUnitDiscExterior := by
  have he := (mobiusBoundaryHomeomorph q).image_closure D
  change (q : Equiv.Perm ExtendedComplex) '' closure D =
    closure ((q : Equiv.Perm ExtendedComplex) '' D) at he
  rw [(q : Equiv.Perm ExtendedComplex).image_compl, he, hq, invariantDisc_closure_unitDisc]
  rfl

/-- The uniqueness clause, with the genuine exterior of a disc. -/
theorem invariant_disc_eq_or_complement_closure (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) {D E : Set ExtendedComplex}
    (hD : IsComplexOpenDisc D) (hE : IsComplexOpenDisc E)
    (hpD : ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' D = D)
    (hpE : ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' E = E) :
    E = D ∨ E = (closure D)ᶜ := by
  have hfront := invariantComplexDiscs_frontier_eq H hH hD hE hpD hpE
  obtain ⟨q, hq, hqfront⟩ := complexDisc_frontier_normalize hD
  have hEqfront : frontier ((q : Equiv.Perm ExtendedComplex) '' E) = complexCircle 0 1 := by
    have he := (mobiusBoundaryHomeomorph q).image_frontier E
    change (q : Equiv.Perm ExtendedComplex) '' frontier E =
      frontier ((q : Equiv.Perm ExtendedComplex) '' E) at he
    rw [← he, ← hfront, hqfront]
  rcases complexDisc_eq_disc_or_exterior_of_unit_frontier (hE.image q) hEqfront with he | he
  · exact Or.inl ((Set.image_injective.mpr (q : Equiv.Perm ExtendedComplex).injective) (he.trans hq.symm))
  · exact Or.inr ((Set.image_injective.mpr (q : Equiv.Perm ExtendedComplex).injective)
      (he.trans (complexDisc_normalize_exterior q hq).symm))

/-- The exterior of a genuine open disc is again a genuine open disc. -/
theorem complexDisc_exterior_isDisc {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D) :
    IsComplexOpenDisc (closure D)ᶜ := by
  obtain ⟨q, hq⟩ := hD.normalize
  have hu : IsComplexOpenDisc Hyperbolic.extendedUnitDisc := by simpa only [hq] using hD.image q
  have hex : IsComplexOpenDisc extendedUnitDiscExterior := by
    simpa only [reciprocalMobius_coe, reciprocal_image_disc] using hu.image reciprocalMobius
  have hi : IsComplexOpenDisc ((q : Equiv.Perm ExtendedComplex) '' (closure D)ᶜ) := by
    rwa [complexDisc_normalize_exterior q hq]
  have hback := hi.image q⁻¹
  rw [Set.image_image] at hback
  change IsComplexOpenDisc ((fun z => (q : Equiv.Perm ExtendedComplex).symm
    ((q : Equiv.Perm ExtendedComplex) z)) '' (closure D)ᶜ) at hback
  simpa only [Equiv.symm_apply_apply, Set.image_id'] using hback

/-- Invariance of a disc includes invariance of its actual exterior. -/
theorem invariantComplexDisc_exterior (H : Subgroup complexMobiusGroup)
    {D : Set ExtendedComplex}
    (hp : ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' D = D) :
    ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' (closure D)ᶜ = (closure D)ᶜ := by
  intro f
  have he := (mobiusBoundaryHomeomorph f.val).image_closure D
  change (f.val : Equiv.Perm ExtendedComplex) '' closure D =
    closure ((f.val : Equiv.Perm ExtendedComplex) '' D) at he
  rw [(f.val : Equiv.Perm ExtendedComplex).image_compl, he, hp f]

/-- All invariant discs, including the existence of both complementary choices. -/
theorem invariant_discs_eq_disc_and_complement_closure (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpD : ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' D = D) :
    {E : Set ExtendedComplex | IsComplexOpenDisc E ∧
      ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' E = E} = {D, (closure D)ᶜ} := by
  ext E
  constructor
  · rintro ⟨hE, hpE⟩
    exact (Set.mem_insert_iff).mpr ((invariant_disc_eq_or_complement_closure H hH hD hE hpD hpE).imp_right
      (fun h => Set.mem_singleton_iff.mpr h))
  · intro hE
    rcases Set.mem_insert_iff.mp hE with rfl | hE
    · exact ⟨hD, hpD⟩
    · rw [Set.mem_singleton_iff] at hE
      subst E
      exact ⟨complexDisc_exterior_isDisc hD, invariantComplexDisc_exterior H hpD⟩

/-- A nonempty open disc and its exterior are distinct. -/
theorem complexDisc_ne_exterior {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D) :
    D ≠ (closure D)ᶜ := by
  obtain ⟨z, hz⟩ := hD.isConnected.nonempty
  intro he
  have hc : z ∈ (closure D)ᶜ := he ▸ hz
  exact hc (subset_closure hz)

/-- Precisely two actual invariant discs occur whenever the non-elementary group has any. -/
theorem invariant_discs_ncard_eq_two (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) (hD : HasInvariantComplexDisc H) :
    {D : Set ExtendedComplex | IsComplexOpenDisc D ∧
      ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' D = D}.ncard = 2 := by
  obtain ⟨D, hD, hpD⟩ := hD
  rw [invariant_discs_eq_disc_and_complement_closure H hH hD hpD]
  exact Set.ncard_pair (complexDisc_ne_exterior hD)

open scoped Pointwise

/-- Translations compose according to their actual complex displacement. -/
theorem invariantDisc_translation_mul (a b : ℂ) :
    DiscreteGroups.mobiusTranslation a * DiscreteGroups.mobiusTranslation b = DiscreteGroups.mobiusTranslation (a
      + b) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  induction z using OnePoint.rec with
  | infty => simp [Equiv.Perm.mul_apply, DiscreteGroups.mobiusTranslation_infty]
  | coe z =>
    change (DiscreteGroups.mobiusTranslation a : Equiv.Perm ExtendedComplex)
      ((DiscreteGroups.mobiusTranslation b : Equiv.Perm ExtendedComplex) z) = _
    simp only [DiscreteGroups.mobiusTranslation_coe]
    congr 1
    ring

/-- Inverse translation, as equality in the actual geometric group. -/
theorem invariantDisc_translation_inv (a : ℂ) :
    (DiscreteGroups.mobiusTranslation a)⁻¹ = DiscreteGroups.mobiusTranslation (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [invariantDisc_translation_mul, add_neg_cancel]
  exact (DiscreteGroups.mobiusTranslation_eq_one_iff 0).mpr rfl

/-- All complex translations form a subgroup of the true Mobius group. -/
def complexTranslationGroup : Subgroup complexMobiusGroup where
  carrier := {f | ∃ b : ℂ, f = DiscreteGroups.mobiusTranslation b}
  one_mem' := ⟨0, ((DiscreteGroups.mobiusTranslation_eq_one_iff 0).mpr rfl).symm⟩
  mul_mem' := by
    rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, invariantDisc_translation_mul a b⟩
  inv_mem' := by
    rintro f ⟨a, rfl⟩
    exact ⟨-a, invariantDisc_translation_inv a⟩

/-- Every genuine translation is either the identity or parabolic. -/
theorem invariantDisc_translation_identity_or_parabolic (a : ℂ) :
    DiscreteGroups.mobiusTranslation a = 1 ∨ MobiusParabolic (DiscreteGroups.mobiusTranslation a) := by
  by_cases ha : a = 0
  · exact Or.inl ((DiscreteGroups.mobiusTranslation_eq_one_iff a).mpr ha)
  · exact Or.inr ((DiscreteGroups.mobiusTranslation_parabolic_iff a).mpr ha)

/-- Translation groups contain no loxodromic elements at all. -/
theorem complexTranslationGroup_not_loxodromic (f : complexTranslationGroup) :
    ¬MobiusLoxodromic f.val := by
  obtain ⟨a, ha⟩ := f.property
  rw [ha]
  rcases invariantDisc_translation_identity_or_parabolic a with he | hp
  · intro hl
    exact hl.1 he
  · exact fun hl => hl.not_parabolic hp

/-- A subgroup of translations is elementary, with the genuine common boundary fixed point infinity. -/
theorem isElementary_of_le_complexTranslationGroup (H : Subgroup complexMobiusGroup)
    (hH : H ≤ complexTranslationGroup) : DiscreteGroups.IsElementary H := by
  apply DiscreteGroups.isElementary_of_boundary_fixed H ∞
  intro f
  obtain ⟨a, ha⟩ := hH f.property
  change (f.val : Equiv.Perm ExtendedComplex) ∞ = ∞
  rw [ha, DiscreteGroups.mobiusTranslation_infty]

/-- The source's two-generator elementary subgroup, with independent real and imaginary translations. -/
def squareTranslationGroup : Subgroup complexMobiusGroup :=
  Subgroup.closure {DiscreteGroups.mobiusTranslation 1, DiscreteGroups.mobiusTranslation Complex.I}

theorem squareTranslationGroup_le_translations : squareTranslationGroup ≤ complexTranslationGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro f (rfl | rfl)
  · exact ⟨1, rfl⟩
  · exact ⟨Complex.I, rfl⟩

theorem squareTranslationGroup_isElementary : DiscreteGroups.IsElementary squareTranslationGroup :=
  isElementary_of_le_complexTranslationGroup _ squareTranslationGroup_le_translations

theorem squareTranslationGroup_not_loxodromic (f : squareTranslationGroup) :
    ¬MobiusLoxodromic f.val :=
  complexTranslationGroup_not_loxodromic ⟨f.val, squareTranslationGroup_le_translations f.property⟩

/-- A genuine disc preserved by unit translation admits only horizontal preserving translations. -/
theorem complexDisc_preserved_translation_im_eq_zero {D : Set ExtendedComplex}
    (hD : IsComplexOpenDisc D)
    (hp1 : (DiscreteGroups.mobiusTranslation 1 : Equiv.Perm ExtendedComplex) '' D = D)
    {b : ℂ} (hpb : (DiscreteGroups.mobiusTranslation b : Equiv.Perm ExtendedComplex) '' D = D) : b.im = 0 := by
  have hinfty : ∞ ∈ frontier D := mobiusParabolic_fixed_mem_disc_frontier
    (DiscreteGroups.mobiusTranslation 1) ((DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero)
    hD hp1 (DiscreteGroups.mobiusTranslation_infty 1)
  rcases (isComplexGeneralizedCircle_iff (frontier D)).mp
    (complexDisc_frontier_isGeneralized hD) with ⟨c, r, _, he⟩ | ⟨a, t, ha, he⟩
  · rw [he] at hinfty
    exact (complexCircle_infty c r hinfty).elim
  · have hstable (f : complexMobiusGroup) (hf : (f : Equiv.Perm ExtendedComplex) '' D = D) :
        (f : Equiv.Perm ExtendedComplex) '' frontier D = frontier D := by
      have hh := (mobiusBoundaryHomeomorph f).image_frontier D
      change (f : Equiv.Perm ExtendedComplex) '' frontier D =
        frontier ((f : Equiv.Perm ExtendedComplex) '' D) at hh
      rwa [hf] at hh
    let z : ℂ := (t / ‖a‖ ^ 2) • a
    have hz : inner ℝ z a = t := by
      simp only [z, real_inner_smul_left, real_inner_self_eq_norm_sq]
      exact div_mul_cancel₀ t (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha))
    have hmem : (z : ExtendedComplex) ∈ frontier D := by
      rw [he, complexLine_coe]
      exact hz
    have htrans (v : ℂ) (hv : (DiscreteGroups.mobiusTranslation v : Equiv.Perm ExtendedComplex) '' D = D) :
        inner ℝ v a = 0 := by
      have hm : ((z + v : ℂ) : ExtendedComplex) ∈ frontier D := by
        rw [← hstable _ hv]
        exact ⟨(z : ExtendedComplex), hmem, DiscreteGroups.mobiusTranslation_coe v z⟩
      rw [he, complexLine_coe, inner_add_left, hz] at hm
      linarith
    have hr := htrans 1 hp1
    have hi := htrans b hpb
    have har : a.re = 0 := by simpa [Complex.inner] using hr
    have hai : a.im ≠ 0 := by
      intro hai
      exact ha (Complex.ext (by simpa using har) (by simpa using hai))
    have heq : a.im * b.im = 0 := by
      simpa [Complex.inner, Complex.mul_re, har] using hi
    exact (mul_eq_zero.mp heq).resolve_left hai

/-- Independent translations cannot preserve any genuine generalized open disc. -/
theorem no_invariant_disc_of_independent_translations (H : Subgroup complexMobiusGroup)
    (h1 : DiscreteGroups.mobiusTranslation 1 ∈ H) (hI : DiscreteGroups.mobiusTranslation Complex.I ∈ H) :
    ¬HasInvariantComplexDisc H := by
  rintro ⟨D, hD, hp⟩
  have he := complexDisc_preserved_translation_im_eq_zero hD (hp ⟨_, h1⟩) (hp ⟨_, hI⟩)
  simp at he

theorem squareTranslationGroup_no_invariant_disc : ¬HasInvariantComplexDisc squareTranslationGroup :=
  no_invariant_disc_of_independent_translations _
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

/-- A real-parameter family of genuine half-discs obtained by vertical translation. -/
def translatedInvariantHalfDisc (t : ℝ) : Set ExtendedComplex :=
  (DiscreteGroups.mobiusTranslation ((t : ℂ) * Complex.I) : Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc

theorem translatedInvariantHalfDisc_isDisc (t : ℝ) :
    IsComplexOpenDisc (translatedInvariantHalfDisc t) :=
  standardComplexHalfDisc_isDisc.image _

/-- Unit translation preserves the unshifted genuine half-disc. -/
theorem unitTranslation_preserves_standardHalfDisc :
    (DiscreteGroups.mobiusTranslation 1 : Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc =
      standardComplexHalfDisc := by
  have he : DiscreteGroups.mobiusTranslation 1 = mobiusSpecialLinearProjection invariantDiscTranslationLift := by
    rw [invariantDiscTranslationLift_projection]
    apply Subtype.ext
    apply Equiv.ext
    intro z
    induction z using OnePoint.rec with
    | infty => rw [DiscreteGroups.mobiusTranslation_infty, mobiusStandardElement_infty]
    | coe z => simp [DiscreteGroups.mobiusTranslation_coe, mobiusStandardElement_coe]
  rw [he]
  apply specialLinear_real_preserves_halfDisc
  intro i j
  fin_cases i <;> fin_cases j <;> simp [invariantDiscTranslationLift]

/-- Unit translation preserves every vertical translate of that actual half-disc. -/
theorem unitTranslation_preserves_translatedHalfDisc (t : ℝ) :
    (DiscreteGroups.mobiusTranslation 1 : Equiv.Perm ExtendedComplex) '' translatedInvariantHalfDisc t =
      translatedInvariantHalfDisc t := by
  unfold translatedInvariantHalfDisc
  have hc : DiscreteGroups.mobiusTranslation 1 * DiscreteGroups.mobiusTranslation ((t : ℂ) * Complex.I) =
      DiscreteGroups.mobiusTranslation ((t : ℂ) * Complex.I) * DiscreteGroups.mobiusTranslation 1 := by
    simp only [invariantDisc_translation_mul, add_comm]
  calc
    _ = ((DiscreteGroups.mobiusTranslation 1 * DiscreteGroups.mobiusTranslation ((t : ℂ) * Complex.I) :
        complexMobiusGroup) : Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc := by
      rw [Set.image_image]
      rfl
    _ = ((DiscreteGroups.mobiusTranslation ((t : ℂ) * Complex.I) * DiscreteGroups.mobiusTranslation 1 :
        complexMobiusGroup) : Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc := by rw [hc]
    _ = (DiscreteGroups.mobiusTranslation ((t : ℂ) * Complex.I) : Equiv.Perm ExtendedComplex) ''
        ((DiscreteGroups.mobiusTranslation 1 : Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [unitTranslation_preserves_standardHalfDisc]

/-- Distinct real heights give distinct actual invariant discs. -/
theorem translatedInvariantHalfDisc_injective : Function.Injective translatedInvariantHalfDisc := by
  intro r s he
  have hshift : (DiscreteGroups.mobiusTranslation (((r - s : ℝ) : ℂ) * Complex.I) :
      Equiv.Perm ExtendedComplex) '' translatedInvariantHalfDisc s = translatedInvariantHalfDisc r := by
    unfold translatedInvariantHalfDisc
    rw [Set.image_image]
    change ((DiscreteGroups.mobiusTranslation (((r - s : ℝ) : ℂ) * Complex.I) *
      DiscreteGroups.mobiusTranslation ((s : ℂ) * Complex.I) : complexMobiusGroup) :
        Equiv.Perm ExtendedComplex) '' standardComplexHalfDisc = _
    rw [invariantDisc_translation_mul]
    have hz : (((r - s : ℝ) : ℂ) * Complex.I + (s : ℂ) * Complex.I) =
        (r : ℂ) * Complex.I := by push_cast; ring
    rw [hz]
  have hzero := complexDisc_preserved_translation_im_eq_zero (translatedInvariantHalfDisc_isDisc s)
    (unitTranslation_preserves_translatedHalfDisc s) (hshift.trans he)
  have hreal : r - s = 0 := by simpa using hzero
  exact sub_eq_zero.mp hreal

/-- The source's cyclic subgroup generated by one real translation. -/
def cyclicUnitTranslationGroup : Subgroup complexMobiusGroup :=
  Subgroup.zpowers (DiscreteGroups.mobiusTranslation 1)

theorem cyclicUnitTranslationGroup_isElementary : DiscreteGroups.IsElementary cyclicUnitTranslationGroup := by
  apply isElementary_of_le_complexTranslationGroup
  apply Subgroup.zpowers_le.mpr
  exact ⟨1, rfl⟩

/-- The entire cyclic group, including inverse powers, preserves each member of the family. -/
theorem cyclicUnitTranslationGroup_preserves_translatedHalfDisc (t : ℝ)
    (f : cyclicUnitTranslationGroup) :
    (f.val : Equiv.Perm ExtendedComplex) '' translatedInvariantHalfDisc t =
      translatedInvariantHalfDisc t := by
  let K : Subgroup complexMobiusGroup :=
    MulAction.stabilizer complexMobiusGroup (translatedInvariantHalfDisc t)
  have hK : DiscreteGroups.mobiusTranslation 1 ∈ K := unitTranslation_preserves_translatedHalfDisc t
  have hle : cyclicUnitTranslationGroup ≤ K := Subgroup.zpowers_le.mpr hK
  exact hle f.property

/-- One translation gives infinitely many genuine invariant discs, despite being elementary. -/
theorem cyclicUnitTranslationGroup_infinitely_many_invariant_discs :
    {D : Set ExtendedComplex | IsComplexOpenDisc D ∧
      ∀ f : cyclicUnitTranslationGroup, (f.val : Equiv.Perm ExtendedComplex) '' D = D}.Infinite := by
  apply (Set.infinite_range_of_injective translatedInvariantHalfDisc_injective).mono
  rintro D ⟨t, rfl⟩
  exact ⟨translatedInvariantHalfDisc_isDisc t, cyclicUnitTranslationGroup_preserves_translatedHalfDisc t⟩

end LowDimensionalTopology.Geometry.Mobius
