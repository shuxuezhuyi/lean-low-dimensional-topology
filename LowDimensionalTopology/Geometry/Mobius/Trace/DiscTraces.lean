/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc

public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperbolicExamples
public import LowDimensionalTopology.Geometry.Inversive.GeneralizedSpheres
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexCircles
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Invariant round boundaries and the squared traces of disc-preserving Mobius maps -/

@[expose] public section

open Set Function
open scoped OnePoint ComplexConjugate Pointwise RealInnerProductSpace

namespace LowDimensionalTopology.Geometry.Mobius

noncomputable section

section InvariantDiscGroups
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
/-- A genuine Mobius map preserving a generalized sphere commutes with its reflection. -/
theorem reflection_commutes_of_invariant_sphere {n : ℕ} [NeZero n]
    (g r : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (hr : Inversive.IsReflection r) (hS : g '' Function.fixedPoints r = Function.fixedPoints r)
    (z : Inversive.ExtendedEuclidean n) : g (r z) = r (g z) := by
  have heq : g * r * g⁻¹ = r :=
    (Inversive.generalMobius_conjugate_isReflection hg hr).eq_of_fixedPoints hr
      (by rw [Inversive.fixedPoints_homeomorph_conjugation, hS])
  have h := congrArg (fun f : Inversive.ExtendedHomeomorph n => f (g z)) heq
  simpa using h

/-- Reflection in an invariant generalized sphere sends fixed points to fixed points. -/
theorem reflection_fixed_of_invariant_sphere {n : ℕ} [NeZero n]
    (g r : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (hr : Inversive.IsReflection r) (hS : g '' Function.fixedPoints r = Function.fixedPoints r)
    {z : Inversive.ExtendedEuclidean n} (hz : g z = z) : g (r z) = r z := by
  rw [reflection_commutes_of_invariant_sphere g r hg hr hS z, hz]

/-- A unique fixed point lies on every invariant generalized sphere. -/
theorem unique_fixed_mem_invariant_sphere {n : ℕ} [NeZero n]
    (g : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (S : Set (Inversive.ExtendedEuclidean n)) (hS : Inversive.IsGeneralizedSphere S)
    (hinv : g '' S = S) {z : Inversive.ExtendedEuclidean n}
    (hunique : ∀ w, g w = w ↔ w = z) : z ∈ S := by
  obtain ⟨r, hr, hrS⟩ := (Inversive.isGeneralizedSphere_iff_fixedPoints_reflection S).mp hS
  have hinv' : g '' Function.fixedPoints r = Function.fixedPoints r := by rw [hrS, hinv]
  have hz : g z = z := (hunique z).mpr rfl
  have hrz : r z = z := (hunique (r z)).mp
    (reflection_fixed_of_invariant_sphere g r hg hr hinv' hz)
  rw [← hrS]
  exact hrz

/-- The inverse point of a fixed point is fixed, expressed using the actual inverse-pair relation. -/
theorem inverse_pair_fixed_of_invariant_sphere {n : ℕ} [NeZero n]
    (g : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (S : Set (Inversive.ExtendedEuclidean n)) (hinv : g '' S = S)
    {z w : Inversive.ExtendedEuclidean n} (hzw : Inversive.IsInversePair S z w) (hz : g z = z) :
    g w = w := by
  obtain ⟨r, hr, hrS, hrz⟩ := hzw
  have hinv' : g '' Function.fixedPoints r = Function.fixedPoints r := by rw [hrS, hinv]
  rw [← hrz]
  exact reflection_fixed_of_invariant_sphere g r hg hr hinv' hz

/-- The unique fixed point of a Mobius map preserving a domain with round boundary lies on that boundary. -/
theorem unique_fixed_mem_boundary_of_invariant_domain {n : ℕ} [NeZero n]
    (g : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (D : Set (Inversive.ExtendedEuclidean n)) (hround : Inversive.IsGeneralizedSphere (frontier D))
    (hinv : g '' D = D) {z : Inversive.ExtendedEuclidean n}
    (hunique : ∀ w, g w = w ↔ w = z) : z ∈ frontier D := by
  apply unique_fixed_mem_invariant_sphere g hg (frontier D) hround _ hunique
  rw [g.image_frontier, hinv]

/-- Mobius maps preserving a domain also preserve inverse pairs for its round boundary. -/
theorem inverse_pair_fixed_of_invariant_domain {n : ℕ} [NeZero n]
    (g : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (D : Set (Inversive.ExtendedEuclidean n)) (hinv : g '' D = D)
    {z w : Inversive.ExtendedEuclidean n} (hzw : Inversive.IsInversePair (frontier D) z w) (hz : g z = z) :
    g w = w := by
  apply inverse_pair_fixed_of_invariant_sphere g hg (frontier D) _ hzw hz
  rw [g.image_frontier, hinv]

/-- Every disc-preserving fractional linear map has nonnegative real squared trace. -/
theorem fractional_disc_preserver_squaredTrace (f : fractionalLinearGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc) :
    ∃ t : ℝ, 0 ≤ t ∧ fractionalSquaredTrace f = (t : ℂ) := by
  obtain ⟨A, hA⟩ := specialLinearProjection_surjective f
  have hAg : fractionalLinear (Matrix.SpecialLinearGroup.toGL A) =
      (f : Equiv.Perm ExtendedComplex) := congrArg Subtype.val hA
  have hpresA : fractionalLinear (Matrix.SpecialLinearGroup.toGL A) '' Hyperbolic.extendedUnitDisc =
      Hyperbolic.extendedUnitDisc := by rw [hAg]; exact hpres
  obtain ⟨_, hd, _⟩ := Hyperbolic.specialLinear_disc_coefficients A hpresA
  refine ⟨(2 * (A 0 0).re) ^ 2, sq_nonneg _, ?_⟩
  rw [← hA, fractionalSquaredTrace_specialLinearProjection, Matrix.trace_fin_two, hd]
  have htrace : A 0 0 + conj (A 0 0) = ((2 * (A 0 0).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
      ring
    · simp
  rw [htrace, ← Complex.ofReal_pow]

/-- The same nonnegative-real trace restriction holds for the actual geometric Mobius group. -/
theorem mobius_disc_preserver_squaredTrace (f : complexMobiusGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc) :
    ∃ t : ℝ, 0 ≤ t ∧ mobiusSquaredTrace f = (t : ℂ) := by
  apply fractional_disc_preserver_squaredTrace (complexMobiusEquivFractionalLinear f)
  simpa only [complexMobiusEquivFractionalLinear_apply] using hpres


/-- A finite fixed point satisfies the actual fractional-linear equation, with nonzero denominator. -/
theorem normalized_disc_fixed_equation {a c : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) {z : ℂ}
    (hfix : Hyperbolic.normalizedDiscTransformation a c hdet (z : ExtendedComplex) = z) :
    c * z + conj a ≠ 0 ∧ a * z + conj c = (c * z + conj a) * z := by
  have hd : c * z + conj a ≠ 0 := by
    intro hd
    rw [Hyperbolic.normalizedDiscTransformation_coe, ite_eq_left hd] at hfix
    exact (OnePoint.coe_ne_infty z) hfix.symm
  have hquot : (a * z + conj c) / (c * z + conj a) = z := by
    apply OnePoint.coe_injective
    simpa only [Hyperbolic.normalizedDiscTransformation_coe, ite_eq_right hd,
      Auxiliary.Analysis.discFractionalMap, Auxiliary.Analysis.fractionalLinearMap] using hfix
  exact ⟨hd, by simpa only [mul_comm z] using (div_eq_iff hd).mp hquot⟩

/-- The denominator eigenvalue of a finite fixed point satisfies the matrix characteristic equation. -/
theorem normalized_disc_fixed_characteristic {a c : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) {z : ℂ}
    (hfix : Hyperbolic.normalizedDiscTransformation a c hdet (z : ExtendedComplex) = z) :
    (c * z + conj a) ^ 2 - (a + conj a) * (c * z + conj a) + 1 = 0 := by
  have heq := (normalized_disc_fixed_equation hdet hfix).2
  have hd := Auxiliary.Analysis.discFractional_determinant hdet
  linear_combination -c * heq - hd

/-- A fixed point on the unit circle forces squared trace at least four. -/
theorem normalized_disc_circle_fixed_trace_ge_four {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ = 1)
    (hfix : Hyperbolic.normalizedDiscTransformation a c hdet (z : ExtendedComplex) = z) :
    4 ≤ 4 * a.re ^ 2 := by
  have heq := (normalized_disc_fixed_equation hdet hfix).2
  have hchar := normalized_disc_fixed_characteristic hdet hfix
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  let q : ℂ := c * z + conj a
  have hreal : q = conj q := by
    calc
      q = (q * z) * conj z := by rw [mul_assoc, hzz, mul_one]
      _ = (a * z + conj c) * conj z := by rw [← heq]
      _ = a * (z * conj z) + conj c * conj z := by ring
      _ = a + conj c * conj z := by rw [hzz, mul_one]
      _ = conj q := by simp only [q, map_add, map_mul, Complex.conj_conj]; ring
  have hqi : q.im = 0 := by
    have hi := congrArg Complex.im hreal
    simp only [Complex.conj_im] at hi
    linarith
  change q ^ 2 - (a + conj a) * q + 1 = 0 at hchar
  have hre := congrArg Complex.re hchar
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.conj_re, Complex.one_re, Complex.zero_re, hqi,
    mul_zero, sub_zero] at hre
  nlinarith [sq_nonneg (q.re - a.re)]

/-- Any finite fixed point off the unit circle forces squared trace at most four. -/
theorem normalized_disc_off_circle_fixed_trace_le_four {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ ≠ 1)
    (hfix : Hyperbolic.normalizedDiscTransformation a c hdet (z : ExtendedComplex) = z) :
    4 * a.re ^ 2 ≤ 4 := by
  obtain ⟨hd, heq⟩ := normalized_disc_fixed_equation hdet hfix
  have hquot : Auxiliary.Analysis.discFractionalMap a c z = z := by
    unfold Auxiliary.Analysis.discFractionalMap Auxiliary.Analysis.fractionalLinearMap
    exact (div_eq_iff hd).mpr (by simpa only [mul_comm z] using heq)
  have hdefect := Auxiliary.Analysis.discFractional_defect hdet hd
  rw [hquot] at hdefect
  have hnz : 1 - ‖z‖ ^ 2 ≠ 0 := by
    intro hn
    have hs : ‖z‖ ^ 2 = (1 : ℝ) ^ 2 := by linarith
    exact hz ((sq_eq_sq₀ (norm_nonneg z) zero_le_one).mp hs)
  have hnq : ‖c * z + conj a‖ ^ 2 = 1 := by
    apply (mul_left_cancel₀ hnz)
    have hden : ‖c * z + conj a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
    have hmul := (eq_div_iff hden).mp hdefect
    simpa only [mul_one] using hmul
  let q : ℂ := c * z + conj a
  have hqconj : q * conj q = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnq]
    norm_num
  have hchar := normalized_disc_fixed_characteristic hdet hfix
  change q ^ 2 - (a + conj a) * q + 1 = 0 at hchar
  have htrace : a + conj a = q + conj q := by
    calc
      a + conj a = (a + conj a) * (q * conj q) := by rw [hqconj, mul_one]
      _ = q + conj q := by
        have h := congrArg (fun w : ℂ => w * conj q) hchar
        linear_combination -h + q * hqconj
  have hre := congrArg Complex.re htrace
  simp only [Complex.add_re, Complex.conj_re] at hre
  have hnormSq : Complex.normSq q = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact hnq
  have hnorm : q.re ^ 2 + q.im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two] using hnormSq
  have hare : a.re = q.re := by linarith
  rw [hare]
  nlinarith [sq_nonneg q.im]


/-- The normalized parameters determine the actual projective squared trace. -/
theorem fractional_squaredTrace_of_normalized_disc (f : fractionalLinearGroup) {a c : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1)
    (hf : (f : Equiv.Perm ExtendedComplex) = Hyperbolic.normalizedDiscTransformation a c hdet) :
    fractionalSquaredTrace f = ((4 * a.re ^ 2 : ℝ) : ℂ) := by
  have hf' : f = matrixProjection (coefficientMatrix a (conj c) c (conj a)
      (by rw [Auxiliary.Analysis.discFractional_determinant hdet]; norm_num)) := Subtype.ext hf
  rw [hf', fractionalSquaredTrace_projection, matrixSquaredTrace,
    Matrix.trace_fin_two, Matrix.det_fin_two]
  change (a + conj a) ^ 2 / (a * conj a - conj c * c) = _
  rw [Auxiliary.Analysis.discFractional_determinant hdet, div_one]
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re]
    ring
  · simp only [pow_two, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

/-- A fixed unit-circle point of an arbitrary disc preserver forces squared trace at least four. -/
theorem fractional_disc_circle_fixed_trace_ge_four (f : fractionalLinearGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc)
    {z : ℂ} (hz : ‖z‖ = 1) (hfix : (f : Equiv.Perm ExtendedComplex) z = z) :
    4 ≤ (fractionalSquaredTrace f).re := by
  obtain ⟨a, c, hdet, hf⟩ := Hyperbolic.fractionalLinear_disc_normal_form f hpres
  rw [fractional_squaredTrace_of_normalized_disc f hdet hf, Complex.ofReal_re]
  rw [hf] at hfix
  exact normalized_disc_circle_fixed_trace_ge_four hdet hz hfix

/-- Squared trace below four excludes fixed points on the unit circle. -/
theorem fractional_disc_trace_lt_four_not_fixed_circle (f : fractionalLinearGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc)
    (htrace : (fractionalSquaredTrace f).re < 4) {z : ℂ} (hz : ‖z‖ = 1) :
    (f : Equiv.Perm ExtendedComplex) z ≠ z := by
  intro hfix
  exact (not_lt_of_ge (fractional_disc_circle_fixed_trace_ge_four f hpres hz hfix)) htrace

/-- Any finite fixed point of a disc preserver with squared trace above four lies on the unit circle. -/
theorem fractional_disc_trace_gt_four_finite_fixed_circle (f : fractionalLinearGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc)
    (htrace : 4 < (fractionalSquaredTrace f).re) {z : ℂ}
    (hfix : (f : Equiv.Perm ExtendedComplex) z = z) : ‖z‖ = 1 := by
  by_contra hz
  obtain ⟨a, c, hdet, hf⟩ := Hyperbolic.fractionalLinear_disc_normal_form f hpres
  rw [fractional_squaredTrace_of_normalized_disc f hdet hf, Complex.ofReal_re] at htrace
  rw [hf] at hfix
  exact (not_lt_of_ge (normalized_disc_off_circle_fixed_trace_le_four hdet hz hfix)) htrace

/-- The actual geometric Mobius action has no unit-circle fixed point when its squared trace is below four. -/
theorem mobius_disc_trace_lt_four_not_fixed_circle (f : complexMobiusGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc)
    (htrace : (mobiusSquaredTrace f).re < 4) {z : ℂ} (hz : ‖z‖ = 1) :
    (f : Equiv.Perm ExtendedComplex) z ≠ z := by
  have hpres' : (complexMobiusEquivFractionalLinear f : Equiv.Perm ExtendedComplex) ''
      Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc := by
    simpa only [complexMobiusEquivFractionalLinear_apply] using hpres
  simpa only [complexMobiusEquivFractionalLinear_apply] using
    fractional_disc_trace_lt_four_not_fixed_circle (complexMobiusEquivFractionalLinear f)
      hpres' htrace hz

/-- The finite fixed points of an actual disc-preserving geometric Mobius map with trace above four lie on its boundary. -/
theorem mobius_disc_trace_gt_four_finite_fixed_circle (f : complexMobiusGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc)
    (htrace : 4 < (mobiusSquaredTrace f).re) {z : ℂ}
    (hfix : (f : Equiv.Perm ExtendedComplex) z = z) : ‖z‖ = 1 := by
  have hpres' : (complexMobiusEquivFractionalLinear f : Equiv.Perm ExtendedComplex) ''
      Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc := by
    simpa only [complexMobiusEquivFractionalLinear_apply] using hpres
  apply fractional_disc_trace_gt_four_finite_fixed_circle
    (complexMobiusEquivFractionalLinear f) hpres' htrace
  simpa only [complexMobiusEquivFractionalLinear_apply] using hfix


/-- The genuine boundary-parabolic definition transports to the real Euclidean carrier. -/
theorem mobiusBoundaryParabolic_real_unique_fixed (f : complexMobiusGroup)
    (hp : MobiusBoundaryParabolic f) (g : Inversive.ExtendedHomeomorph 2)
    (hgf : euclideanToComplexHom g = (f : Equiv.Perm ExtendedComplex)) :
    ∃ a : Inversive.ExtendedEuclidean 2, ∀ w, g w = w ↔ w = a := by
  obtain ⟨_, a, ha⟩ := hp
  let e := extendedComplexEuclideanHomeomorph
  refine ⟨e a, fun w => ?_⟩
  have hcoord : e.symm (g w) = (f : Equiv.Perm ExtendedComplex) (e.symm w) := by
    simpa only [e, euclideanToComplexHom_apply, Homeomorph.apply_symm_apply] using
      congrArg (fun q : Equiv.Perm ExtendedComplex => q (e.symm w)) hgf
  rw [← e.symm.injective.eq_iff, hcoord, ha]
  constructor
  · intro hw
    exact (e.apply_symm_apply w).symm.trans (congrArg e hw)
  · rintro rfl
    exact e.symm_apply_apply a

/-- Actual parabolic fixed points lie on the boundary of every preserved domain with round boundary. -/
theorem mobiusBoundaryParabolic_fixed_mem_boundary (f : complexMobiusGroup)
    (hp : MobiusBoundaryParabolic f) (g : Inversive.ExtendedHomeomorph 2)
    (hg : g ∈ Inversive.generalMobiusGroup 2)
    (hgf : euclideanToComplexHom g = (f : Equiv.Perm ExtendedComplex))
    (D : Set (Inversive.ExtendedEuclidean 2)) (hround : Inversive.IsGeneralizedSphere (frontier D))
    (hinv : g '' D = D) {z : Inversive.ExtendedEuclidean 2} (hz : g z = z) :
    z ∈ frontier D := by
  obtain ⟨a, ha⟩ := mobiusBoundaryParabolic_real_unique_fixed f hp g hgf
  have hmem := unique_fixed_mem_boundary_of_invariant_domain g hg D hround hinv ha
  simpa only [(ha z).mp hz] using hmem


/-- A two-point fixed set off an invariant generalized sphere is an inverse pair. -/
theorem fixed_pair_inverse_of_invariant_sphere {n : ℕ} [NeZero n]
    (g : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (S : Set (Inversive.ExtendedEuclidean n)) (hS : Inversive.IsGeneralizedSphere S) (hinv : g '' S = S)
    {z w : Inversive.ExtendedEuclidean n} (hz : z ∉ S)
    (hfixed : ∀ x, g x = x ↔ x = z ∨ x = w) : Inversive.IsInversePair S z w := by
  obtain ⟨r, hr, hrS⟩ := (Inversive.isGeneralizedSphere_iff_fixedPoints_reflection S).mp hS
  have hinv' : g '' Function.fixedPoints r = Function.fixedPoints r := by rw [hrS, hinv]
  have hfixz : g z = z := (hfixed z).mpr (Or.inl rfl)
  have hfixr := reflection_fixed_of_invariant_sphere g r hg hr hinv' hfixz
  have hrz : r z = w := by
    rcases (hfixed (r z)).mp hfixr with heq | heq
    · exact False.elim (hz (by rw [← hrS]; exact heq))
    · exact heq
  exact ⟨r, hr, hrS, hrz⟩

/-- The inverse-pair conclusion for an invariant round-boundary domain. -/
theorem fixed_pair_inverse_of_invariant_domain {n : ℕ} [NeZero n]
    (g : Inversive.ExtendedHomeomorph n) (hg : g ∈ Inversive.generalMobiusGroup n)
    (D : Set (Inversive.ExtendedEuclidean n)) (hround : Inversive.IsGeneralizedSphere (frontier D))
    (hinv : g '' D = D) {z w : Inversive.ExtendedEuclidean n} (hz : z ∉ frontier D)
    (hfixed : ∀ x, g x = x ↔ x = z ∨ x = w) : Inversive.IsInversePair (frontier D) z w := by
  apply fixed_pair_inverse_of_invariant_sphere g hg (frontier D) hround _ hz hfixed
  rw [g.image_frontier, hinv]

/-- All extended fixed points of a disc preserver with squared trace above four lie on the unit circle. -/
theorem fractional_disc_trace_gt_four_fixed_circle (f : fractionalLinearGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc)
    (htrace : 4 < (fractionalSquaredTrace f).re) {z : ExtendedComplex}
    (hfix : (f : Equiv.Perm ExtendedComplex) z = z) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ z = (ζ : ExtendedComplex) := by
  cases z using OnePoint.rec with
  | coe z => exact ⟨z, fractional_disc_trace_gt_four_finite_fixed_circle f hpres htrace hfix, rfl⟩
  | infty =>
    obtain ⟨a, c, hdet, hf⟩ := Hyperbolic.fractionalLinear_disc_normal_form f hpres
    rw [fractional_squaredTrace_of_normalized_disc f hdet hf, Complex.ofReal_re] at htrace
    rw [hf, Hyperbolic.normalizedDiscTransformation_infty] at hfix
    have hc : c = 0 := by
      by_contra hc
      rw [ite_eq_right hc] at hfix
      exact (OnePoint.coe_ne_infty (a / c)) hfix
    rw [hc, Complex.normSq_zero, sub_zero, Complex.normSq_apply] at hdet
    exact False.elim (by nlinarith [sq_nonneg a.im])

/-- The same complete boundary-location conclusion for the actual geometric Mobius group. -/
theorem mobius_disc_trace_gt_four_fixed_circle (f : complexMobiusGroup)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc)
    (htrace : 4 < (mobiusSquaredTrace f).re) {z : ExtendedComplex}
    (hfix : (f : Equiv.Perm ExtendedComplex) z = z) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ z = (ζ : ExtendedComplex) := by
  have hpres' : (complexMobiusEquivFractionalLinear f : Equiv.Perm ExtendedComplex) ''
      Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc := by
    simpa only [complexMobiusEquivFractionalLinear_apply] using hpres
  apply fractional_disc_trace_gt_four_fixed_circle
    (complexMobiusEquivFractionalLinear f) hpres' htrace
  simpa only [complexMobiusEquivFractionalLinear_apply] using hfix

end InvariantDiscGroups


open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius Metric






/-- The actual fractional linear reciprocal, with its already proved compactified continuity. -/
def unitDiscReciprocalHomeomorph : ExtendedComplex ≃ₜ ExtendedComplex where
  toEquiv := reciprocal
  continuous_toFun := continuous_reciprocal
  continuous_invFun := by
    have h : (reciprocal.symm : ExtendedComplex → ExtendedComplex) = reciprocal := by
      funext z
      apply reciprocal.injective
      rw [Equiv.apply_symm_apply, reciprocal_involutive]
    change Continuous (reciprocal.symm : ExtendedComplex → ExtendedComplex)
    rw [h]
    exact continuous_reciprocal











theorem isOpen_unitCircle_compl : IsOpen ((complexCircle 0 1)ᶜ) := by
  rw [unitCircle_compl_eq_disc_union_exterior]
  exact isOpen_extendedUnitDisc.union isOpen_extendedUnitDiscExterior



/-- The two genuine component carriers of the unit-circle complement, in the actual sphere topology. -/
theorem unitCircle_complement_components :
    {S : Set ExtendedComplex | ∃ z ∈ (complexCircle 0 1)ᶜ,
      connectedComponentIn (complexCircle 0 1)ᶜ z = S} =
        {Hyperbolic.extendedUnitDisc, extendedUnitDiscExterior} := by
  ext S
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [unitCircle_compl_eq_disc_union_exterior] at hz
    rcases hz with hz | hz
    · rw [connectedComponentIn_unitCircle_compl_of_mem_disc hz]
      exact mem_insert _ _
    · rw [connectedComponentIn_unitCircle_compl_of_mem_exterior hz]
      exact mem_insert_of_mem _ (mem_singleton _)
  · intro hS
    rcases mem_insert_iff.mp hS with rfl | hS
    · refine ⟨(0 : ℂ), ?_, connectedComponentIn_unitCircle_compl_of_mem_disc ?_⟩
      · rw [unitCircle_compl_eq_disc_union_exterior]
        left
        simp [Hyperbolic.coe_mem_extendedUnitDisc]
      · simp [Hyperbolic.coe_mem_extendedUnitDisc]
    · have heq : S = extendedUnitDiscExterior := mem_singleton_iff.mp hS
      subst S
      refine ⟨∞, ?_, connectedComponentIn_unitCircle_compl_of_mem_exterior infty_mem_extendedUnitDiscExterior⟩
      rw [unitCircle_compl_eq_disc_union_exterior]
      exact Or.inr infty_mem_extendedUnitDiscExterior

theorem extendedUnitDisc_ne_exterior : Hyperbolic.extendedUnitDisc ≠ extendedUnitDiscExterior := by
  intro heq
  have h := infty_mem_extendedUnitDiscExterior
  rw [← heq] at h
  exact infty_not_mem_extendedUnitDisc h

theorem unitCircle_complement_component_count :
    {S : Set ExtendedComplex | ∃ z ∈ (complexCircle 0 1)ᶜ,
      connectedComponentIn (complexCircle 0 1)ᶜ z = S}.ncard = 2 := by
  rw [unitCircle_complement_components]
  exact Set.ncard_pair extendedUnitDisc_ne_exterior

theorem reciprocal_mem_unitCircle_iff (z : ExtendedComplex) :
    reciprocal z ∈ complexCircle 0 1 ↔ z ∈ complexCircle 0 1 := by
  induction z using OnePoint.rec with
  | infty => simp [reciprocal_infty]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [reciprocal_zero]
    · rw [reciprocal_coe z hz]
      simp only [complexCircle_coe, sub_zero, norm_inv, inv_eq_one]

theorem reciprocal_image_unitCircle : reciprocal '' complexCircle 0 1 = complexCircle 0 1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (reciprocal_mem_unitCircle_iff w).mpr hw
  · intro hz
    exact ⟨reciprocal z, (reciprocal_mem_unitCircle_iff z).mpr hz, reciprocal_involutive z⟩


end
end LowDimensionalTopology.Geometry.Mobius
