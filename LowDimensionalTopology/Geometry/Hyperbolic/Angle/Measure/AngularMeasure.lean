module
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ModelCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCosineRule
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic

/-! # Genuine local angular measure and geometric angles in the native disc -/

@[expose] public section
noncomputable section
open Set Topology MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Pointwise OnePoint Complex.UnitDisc ENNReal ComplexConjugate Classical UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The entire actual unit circle fixes the usual normalization of angular Haar measure. -/
def polygonDirectionPositiveCompact : PositiveCompacts Circle :=
  ⟨⟨univ, isCompact_univ⟩, by simp⟩

/-- The genuine angular probability measure on the Euclidean unit tangent circle. -/
def polygonDirectionMeasure : Measure Circle := haarMeasure polygonDirectionPositiveCompact

instance polygonDirectionMeasure_isHaar : IsHaarMeasure polygonDirectionMeasure := by
  unfold polygonDirectionMeasure
  infer_instance

theorem polygonDirectionMeasure_univ : polygonDirectionMeasure univ = 1 := haarMeasure_self

instance polygonDirectionMeasure_isProbability : IsProbabilityMeasure polygonDirectionMeasure :=
  ⟨polygonDirectionMeasure_univ⟩

instance polygonDirectionMeasure_nullSingleton : NullSingletonClass polygonDirectionMeasure := by
  let : Nontrivial Circle := ⟨⟨1, -1, by
    intro h
    have he := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at he⟩⟩
  infer_instance

/-- An actual radial point of the original Poincare disc, with genuine unit-circle direction. -/
def discRadialPoint (r : Ioo (0 : ℝ) 1) (u : Circle) : Complex.UnitDisc :=
  Complex.UnitDisc.mk ((r.val : ℂ) * (u : ℂ)) (by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r.property.1, Circle.norm_coe, mul_one]
    exact r.property.2)

theorem continuous_discRadialPoint (r : Ioo (0 : ℝ) 1) : Continuous (discRadialPoint r) := by
  apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
  exact continuous_const.mul continuous_subtype_val

/-- Actual ray directions whose positive native radial segment meets the given original disc set. -/
def discRadialDirections (S : Set Complex.UnitDisc) : Set Circle :=
  {u | ∃ r : Ioo (0 : ℝ) 1, discRadialPoint r u ∈ S}

/-- A genuine hyperbolic disc automorphism sending the specified original point to zero. -/
def discOriginNormalizer (z : Complex.UnitDisc) : Complex.UnitDisc ≃ₜ Complex.UnitDisc :=
  (discSL2Homeomorph (discToHalfPlane z).toSL2R).symm

theorem discOriginNormalizer_apply_self (z : Complex.UnitDisc) : discOriginNormalizer z z = 0 := by
  apply (discSL2Homeomorph (discToHalfPlane z).toSL2R).injective
  change (discSL2Homeomorph (discToHalfPlane z).toSL2R)
    ((discSL2Homeomorph (discToHalfPlane z).toSL2R).symm z) = _
  rw [Homeomorph.apply_symm_apply]
  exact (discSL2Equiv_center z).symm

theorem discOriginNormalizer_isometry (z : Complex.UnitDisc) :
    letI := discHyperbolicMetric; Isometry (discOriginNormalizer z) := by
  let := discHyperbolicMetric
  change Isometry (discSL2Action ((discToHalfPlane z).toSL2R)⁻¹)
  exact discSL2Action_isometry _

theorem discRadialPoint_norm (r : Ioo (0 : ℝ) 1) (u : Circle) :
    ‖(discRadialPoint r u : ℂ)‖ = r.val := by
  change ‖(r.val : ℂ) * (u : ℂ)‖ = r.val
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r.property.1,
    Circle.norm_coe, mul_one]

theorem kleinCoordinate_discRadialPoint (r : Ioo (0 : ℝ) 1) (u : Circle) :
    kleinCoordinate (discRadialPoint r u) = ((2 * r.val / (1 + r.val ^ 2) : ℝ) : ℂ) * (u : ℂ) := by
  change kleinFormula (discRadialPoint r u : ℂ) = _
  rw [kleinFormula, discRadialPoint_norm]
  change ((2 / (1 + r.val ^ 2) : ℝ) : ℂ) * ((r.val : ℂ) * (u : ℂ)) = _
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  ring

theorem discRadialPoint_mem_of_le {S : Set Complex.UnitDisc} (hS : DiscHConvex S)
    (h0 : (0 : Complex.UnitDisc) ∈ S) {r s : Ioo (0 : ℝ) 1} (hsr : s.val ≤ r.val)
    (u : Circle) (hr : discRadialPoint r u ∈ S) : discRadialPoint s u ∈ S := by
  let R := 2 * r.val / (1 + r.val ^ 2)
  let T := 2 * s.val / (1 + s.val ^ 2)
  have hR : 0 < R := by exact div_pos (mul_pos (by norm_num) r.property.1) (by positivity)
  have hT : 0 < T := by exact div_pos (mul_pos (by norm_num) s.property.1) (by positivity)
  have hTR : T ≤ R := by
    dsimp [T, R]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hmul : 0 ≤ (r.val - s.val) * (1 - r.val * s.val) := by
      apply mul_nonneg (sub_nonneg.mpr hsr)
      have : r.val * s.val < 1 := by nlinarith [r.property.1, r.property.2, s.property.1, s.property.2]
      linarith
    nlinarith
  have hconv := (discHConvex_iff_klein_convex S).mp hS
  have hz : (0 : ℂ) ∈ kleinCoordinate '' S := by
    convert mem_image_of_mem kleinCoordinate h0 using 1
    simp [kleinCoordinate, poincareToKlein, kleinFormula]
  have hq := hconv hz (mem_image_of_mem kleinCoordinate hr)
    (show 0 ≤ 1 - T / R by exact sub_nonneg.mpr ((div_le_one hR).mpr hTR))
    (show 0 ≤ T / R by positivity) (by ring : 1 - T / R + T / R = 1)
  have he : (1 - T / R) • (0 : ℂ) + (T / R) • kleinCoordinate (discRadialPoint r u) =
      kleinCoordinate (discRadialPoint s u) := by
    rw [smul_zero, zero_add, kleinCoordinate_discRadialPoint, kleinCoordinate_discRadialPoint]
    change (T / R : ℝ) • ((R : ℂ) * (u : ℂ)) = (T : ℂ) * (u : ℂ)
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ T hR.ne']
  rw [he] at hq
  obtain ⟨v, hv, heq⟩ := hq
  exact kleinCoordinate_injective heq ▸ hv

/-- A countable cofinal family of genuinely positive radial distances. -/
def discRadialTestRadius (n : ℕ) : Ioo (0 : ℝ) 1 :=
  ⟨1 / ((n : ℝ) + 2), by
    change 0 < 1 / ((n : ℝ) + 2) ∧ 1 / ((n : ℝ) + 2) < 1
    constructor
    · positivity
    · apply (div_lt_one (by positivity)).mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith⟩

theorem exists_discRadialTestRadius_le (r : Ioo (0 : ℝ) 1) :
    ∃ n, (discRadialTestRadius n).val ≤ r.val := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt r.property.1
  refine ⟨n, le_trans ?_ hn.le⟩
  change 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem discRadialDirections_eq_iUnion {S : Set Complex.UnitDisc} (hS : DiscHConvex S)
    (h0 : (0 : Complex.UnitDisc) ∈ S) :
    discRadialDirections S = ⋃ n : ℕ, discRadialPoint (discRadialTestRadius n) ⁻¹' S := by
  ext u
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨n, hn⟩ := exists_discRadialTestRadius_le r
    exact mem_iUnion.mpr ⟨n, discRadialPoint_mem_of_le hS h0 hn u hr⟩
  · intro hu
    obtain ⟨n, hn⟩ := mem_iUnion.mp hu
    exact ⟨discRadialTestRadius n, hn⟩

/-- For an actual closed convex set through the basepoint, actual subtended directions are Borel. -/
theorem measurableSet_discRadialDirections {S : Set Complex.UnitDisc} (hS : DiscHConvex S)
    (hc : IsClosed S) (h0 : (0 : Complex.UnitDisc) ∈ S) : MeasurableSet (discRadialDirections S) := by
  rw [discRadialDirections_eq_iUnion hS h0]
  exact MeasurableSet.iUnion fun n => (hc.preimage (continuous_discRadialPoint _)).measurableSet

theorem finite_circle_orthogonal (n : ℂ) (hn : n ≠ 0) :
    {u : Circle | inner ℝ (u : ℂ) n = 0}.Finite := by
  let f : Circle → ℂ := fun u => (u : ℂ) * conj n / (‖n‖ : ℂ)
  have hnR : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hnC : (‖n‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnR
  have hfi : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply mul_right_cancel₀ (show conj n ≠ 0 by simpa using hn)
    exact (div_left_inj' hnC).mp huv
  apply ((Set.toFinite ({Complex.I, -Complex.I} : Set ℂ)).preimage hfi.injOn).subset
  intro u hu
  change f u = Complex.I ∨ f u = -Complex.I
  have hnorm : ‖f u‖ = 1 := by
    dsimp [f]
    rw [norm_div, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg n), div_self hnR]
  have hre : (f u).re = 0 := by
    dsimp [f]
    rw [Complex.div_ofReal_re]
    have he : ((u : ℂ) * conj n).re = inner ℝ (u : ℂ) n := by
      simp [Complex.inner, Complex.mul_re]; ring
    rw [he, hu, zero_div]
  have him : (f u).im = 1 ∨ (f u).im = -1 := by
    have hs := Complex.sq_norm_sub_sq_re (f u)
    rw [hnorm, hre] at hs
    have : ((f u).im) ^ 2 = (1 : ℝ) ^ 2 := by nlinarith
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp this
  rcases him with h | h
  · left; exact Complex.ext (by simpa using hre) (by simpa using h)
  · right; exact Complex.ext (by simpa using hre) (by simpa using h)

theorem discRadialDirections_mono {S T : Set Complex.UnitDisc} (h : S ⊆ T) :
    discRadialDirections S ⊆ discRadialDirections T := by
  rintro u ⟨r, hr⟩
  exact ⟨r, h hr⟩

theorem discRadialDirections_inter {S T : Set Complex.UnitDisc}
    (hS : DiscHConvex S) (hT : DiscHConvex T)
    (h0S : (0 : Complex.UnitDisc) ∈ S) (h0T : (0 : Complex.UnitDisc) ∈ T) :
    discRadialDirections (S ∩ T) = discRadialDirections S ∩ discRadialDirections T := by
  ext u
  constructor
  · rintro ⟨r, hrS, hrT⟩
    exact ⟨⟨r, hrS⟩, ⟨r, hrT⟩⟩
  · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
    rcases le_total r.val s.val with h | h
    · exact ⟨r, hr, discRadialPoint_mem_of_le hT h0T h u hs⟩
    · exact ⟨s, discRadialPoint_mem_of_le hS h0S h u hr, hs⟩

theorem finite_discRadialDirections_of_line (L : DiscLine) (h0 : (0 : Complex.UnitDisc) ∈ L.carrier) :
    (discRadialDirections L.carrier).Finite := by
  obtain ⟨n, t, hn, hline⟩ := L.exists_klein_affine_equation
  have ht : t = 0 := by
    have he := (hline 0).mp h0
    simpa [poincareToKlein, kleinFormula] using he.symm
  apply (finite_circle_orthogonal n hn).subset
  rintro u ⟨r, hr⟩
  have he := (hline _).mp hr
  change inner ℝ (kleinCoordinate (discRadialPoint r u)) n = t at he
  rw [ht, kleinCoordinate_discRadialPoint] at he
  change inner ℝ ((2 * r.val / (1 + r.val ^ 2)) • (u : ℂ)) n = 0 at he
  rw [real_inner_smul_left, mul_eq_zero] at he
  exact he.resolve_left (ne_of_gt (div_pos (mul_pos (by norm_num) r.property.1) (by positivity)))

theorem polygonDirectionMeasure_line_zero (L : DiscLine) (h0 : (0 : Complex.UnitDisc) ∈ L.carrier) :
    polygonDirectionMeasure (discRadialDirections L.carrier) = 0 :=
  (finite_discRadialDirections_of_line L h0).measure_zero _

theorem tendsto_discRadialTestPoint (u : Circle) :
    Filter.Tendsto (fun n => discRadialPoint (discRadialTestRadius n) u)
      Filter.atTop (𝓝 (0 : Complex.UnitDisc)) := by
  apply Complex.UnitDisc.isEmbedding_coe.tendsto_nhds_iff.mpr
  change Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 2) : ℝ) : ℂ) * (u : ℂ)) _ (𝓝 (0 : ℂ))
  have ht : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1) using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  convert (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul_const (u : ℂ) using 1 <;> simp

/-- A true locally finite closed covering gives a full circle of directions in its incident members. -/
theorem discRadialDirections_incident_cover {ι : Type*} (S : ι → Set Complex.UnitDisc)
    (hl : LocallyFinite S) (hc : ∀ i, IsClosed (S i)) (hcov : (⋃ i, S i) = univ) :
    (⋃ i ∈ {i | (0 : Complex.UnitDisc) ∈ S i}, discRadialDirections (S i)) = univ := by
  apply eq_univ_of_forall
  intro u
  have hN := hl.iInter_compl_mem_nhds hc (0 : Complex.UnitDisc)
  obtain ⟨n, hn⟩ := ((tendsto_discRadialTestPoint u).eventually hN).exists
  have hp : discRadialPoint (discRadialTestRadius n) u ∈ ⋃ i, S i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have h0 : (0 : Complex.UnitDisc) ∈ S i := by
    by_contra hz
    exact (mem_iInter₂.mp hn i hz) hi
  exact mem_iUnion₂.mpr ⟨i, h0, ⟨discRadialTestRadius n, hi⟩⟩

/-- Every native hyperbolic isometry fixing the origin acts by an actual rotation or reflected rotation. -/
theorem disc_zero_isometry_formula (f : Complex.UnitDisc → Complex.UnitDisc)
    (hf : let := discHyperbolicMetric; Isometry f) (h0 : f 0 = 0) :
    ∃ u : Circle, (∀ z : Complex.UnitDisc, (f z : ℂ) = (u : ℂ) * (z : ℂ)) ∨
      (∀ z : Complex.UnitDisc, (f z : ℂ) = (u : ℂ) * conj (z : ℂ)) := by
  let := discHyperbolicMetric
  obtain ⟨a, c, hdet, hform⟩ := (disc_isometry_iff_coefficient_formula f).mp hf
  have ha : a ≠ 0 := by
    intro he
    rw [he, norm_zero] at hdet
    nlinarith [sq_nonneg ‖c‖]
  have hac : conj a ≠ 0 := by simpa using ha
  have hc : c = 0 := by
    have hz : (conj c) / (conj a) = 0 := by
      rcases hform with h | h
      · have hz := h 0
        simpa only [h0, Complex.UnitDisc.coe_zero, mul_zero, zero_add, add_zero] using hz.symm
      · have hz := h 0
        simpa only [h0, Complex.UnitDisc.coe_zero, map_zero, mul_zero, zero_add, add_zero] using hz.symm
    have hh : conj c = 0 := (div_eq_zero_iff).mp hz |>.resolve_right hac
    simpa using hh
  have han : ‖a‖ = 1 := by rw [hc, norm_zero] at hdet; nlinarith [norm_nonneg a]
  let u : Circle := ⟨a / conj a, by
    change a / conj a ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [norm_div, Complex.norm_conj, han, div_self (by norm_num : (1 : ℝ) ≠ 0)]⟩
  refine ⟨u, ?_⟩
  rcases hform with h | h
  · left; intro z
    rw [h, hc]
    simp only [map_zero, zero_mul, zero_add, add_zero]
    change a * (z : ℂ) / conj a = (a / conj a) * (z : ℂ)
    ring
  · right; intro z
    rw [h, hc]
    simp only [map_zero, zero_mul, zero_add, add_zero]
    change a * conj (z : ℂ) / conj a = (a / conj a) * conj (z : ℂ)
    ring

theorem discRadialDirections_image_of_commute (f : Complex.UnitDisc ≃ Complex.UnitDisc)
    (e : Circle ≃ Circle) (hc : ∀ (r : Ioo (0 : ℝ) 1) u,
      f (discRadialPoint r u) = discRadialPoint r (e u)) (S : Set Complex.UnitDisc) :
    discRadialDirections (f '' S) = e '' discRadialDirections S := by
  ext u
  constructor
  · rintro ⟨r, z, hz, he⟩
    refine ⟨e.symm u, ⟨r, ?_⟩, e.apply_symm_apply u⟩
    have hq : f (discRadialPoint r (e.symm u)) = f z := by rw [hc, e.apply_symm_apply, he]
    exact f.injective hq ▸ hz
  · rintro ⟨v, ⟨r, hr⟩, rfl⟩
    exact ⟨r, discRadialPoint r v, hr, hc r v⟩

theorem polygonDirectionMeasure_image_homeomorph (e : Circle ≃ₜ Circle)
    (he : MeasurePreserving e polygonDirectionMeasure polygonDirectionMeasure) (S : Set Circle) :
    polygonDirectionMeasure (e '' S) = polygonDirectionMeasure S := by
  conv_lhs => rw [← he.map_eq]
  rw [e.measurableEmbedding.map_apply, e.injective.preimage_image]

/-- Angular Haar measure of actual directions is unchanged by every native isometry fixing the origin. -/
theorem polygonDirectionMeasure_radial_isometry (f : Complex.UnitDisc ≃ₜ Complex.UnitDisc)
    (hf : let := discHyperbolicMetric; Isometry f) (h0 : f 0 = 0) (S : Set Complex.UnitDisc) :
    polygonDirectionMeasure (discRadialDirections (f '' S)) =
      polygonDirectionMeasure (discRadialDirections S) := by
  obtain ⟨u, hu | hu⟩ := disc_zero_isometry_formula f hf h0
  · let e := Homeomorph.mulLeft u
    have hc (r : Ioo (0 : ℝ) 1) (v : Circle) :
        f (discRadialPoint r v) = discRadialPoint r (e v) := by
      apply Complex.UnitDisc.coe_injective
      rw [hu]
      change (u : ℂ) * ((r.val : ℂ) * (v : ℂ)) = (r.val : ℂ) * ((u : ℂ) * (v : ℂ))
      ring
    have hd : discRadialDirections (f '' S) = e '' discRadialDirections S :=
      discRadialDirections_image_of_commute f.toEquiv e.toEquiv hc S
    rw [hd]
    exact polygonDirectionMeasure_image_homeomorph e (measurePreserving_mul_left _ u) _
  · let e := (Homeomorph.inv Circle).trans (Homeomorph.mulLeft u)
    have hc (r : Ioo (0 : ℝ) 1) (v : Circle) :
        f (discRadialPoint r v) = discRadialPoint r (e v) := by
      apply Complex.UnitDisc.coe_injective
      rw [hu]
      change (u : ℂ) * conj ((r.val : ℂ) * (v : ℂ)) = (r.val : ℂ) * ((u : ℂ) * ((v⁻¹ : Circle) : ℂ))
      rw [map_mul, Complex.conj_ofReal, Circle.coe_inv_eq_conj]
      ring
    have hd : discRadialDirections (f '' S) = e '' discRadialDirections S :=
      discRadialDirections_image_of_commute f.toEquiv e.toEquiv hc S
    rw [hd]
    exact polygonDirectionMeasure_image_homeomorph e
      ((measurePreserving_mul_left _ u).comp (measurePreserving_inv _)) _

theorem discOriginNormalizer_symm_isometry (z : Complex.UnitDisc) :
    let := discHyperbolicMetric; Isometry (discOriginNormalizer z).symm := by
  let := discHyperbolicMetric
  change Isometry (discSL2Action (discToHalfPlane z).toSL2R)
  exact discSL2Action_isometry _

/-- Actual angular fraction subtended by a native disc set at its actual basepoint. -/
def discSubtendedAngularFraction (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) : ℝ≥0∞ :=
  polygonDirectionMeasure (discRadialDirections (discOriginNormalizer z '' S))

/-- The actual native-disc angle in radians, obtained from angular Haar measure rather than prescribed angle data. -/
def discSubtendedAngle (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) : ℝ :=
  2 * Real.pi * (discSubtendedAngularFraction S z).toReal

/-- Native isometries preserve the actual angular fraction at the transported original basepoint. -/
theorem discSubtendedAngularFraction_isometry (f : Complex.UnitDisc ≃ₜ Complex.UnitDisc)
    (hf : let := discHyperbolicMetric; Isometry f) (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) :
    discSubtendedAngularFraction (f '' S) (f z) = discSubtendedAngularFraction S z := by
  let := discHyperbolicMetric
  let e := ((discOriginNormalizer z).symm.trans f).trans (discOriginNormalizer (f z))
  have he : Isometry e := (discOriginNormalizer_isometry (f z)).comp
    (hf.comp (discOriginNormalizer_symm_isometry z))
  have he0 : e 0 = 0 := by
    change discOriginNormalizer (f z) (f ((discOriginNormalizer z).symm 0)) = 0
    have hz : (discOriginNormalizer z).symm 0 = z := by
      apply (discOriginNormalizer z).injective
      rw [Homeomorph.apply_symm_apply, discOriginNormalizer_apply_self]
    rw [hz, discOriginNormalizer_apply_self]
  have hset : discOriginNormalizer (f z) '' (f '' S) =
      e '' (discOriginNormalizer z '' S) := by
    simp only [image_image]
    congr 1
    funext q
    simp only [e, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  unfold discSubtendedAngularFraction
  rw [hset]
  exact polygonDirectionMeasure_radial_isometry e he he0 _

theorem discSubtendedAngle_isometry (f : Complex.UnitDisc ≃ₜ Complex.UnitDisc)
    (hf : let := discHyperbolicMetric; Isometry f) (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) :
    discSubtendedAngle (f '' S) (f z) = discSubtendedAngle S z := by
  rw [discSubtendedAngle, discSubtendedAngle, discSubtendedAngularFraction_isometry f hf]

theorem discRadialDirections_of_mem_nhds {S : Set Complex.UnitDisc}
    (hS : S ∈ 𝓝 (0 : Complex.UnitDisc)) : discRadialDirections S = univ := by
  apply eq_univ_of_forall
  intro u
  obtain ⟨n, hn⟩ := ((tendsto_discRadialTestPoint u).eventually hS).exists
  exact ⟨discRadialTestRadius n, hn⟩

/-- Angular fractions give exactly the full angle at genuine interior points. -/
theorem discSubtendedAngularFraction_of_interior {S : Set Complex.UnitDisc} {z : Complex.UnitDisc}
    (hz : z ∈ interior S) : discSubtendedAngularFraction S z = 1 := by
  unfold discSubtendedAngularFraction
  apply Eq.trans (congrArg polygonDirectionMeasure (discRadialDirections_of_mem_nhds ?_))
    polygonDirectionMeasure_univ
  have hn := (discOriginNormalizer z).isOpenMap.image_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
  rwa [discOriginNormalizer_apply_self] at hn

theorem discSubtendedAngle_of_interior {S : Set Complex.UnitDisc} {z : Complex.UnitDisc}
    (hz : z ∈ interior S) : discSubtendedAngle S z = 2 * Real.pi := by
  rw [discSubtendedAngle, discSubtendedAngularFraction_of_interior hz, ENNReal.toReal_one, mul_one]

/-- In an actual convex region, the angular measure uses only its germ at the point. -/
theorem discRadialDirections_inter_nhds {S N : Set Complex.UnitDisc} (hS : DiscHConvex S)
    (h0 : (0 : Complex.UnitDisc) ∈ S) (hN : N ∈ 𝓝 (0 : Complex.UnitDisc)) :
    discRadialDirections (S ∩ N) = discRadialDirections S := by
  apply subset_antisymm (discRadialDirections_mono inter_subset_left)
  rintro u ⟨r, hr⟩
  have ht := ((continuous_norm.comp Complex.UnitDisc.continuous_coe).continuousAt.tendsto).comp
    (tendsto_discRadialTestPoint u)
  have htr : Filter.Tendsto (fun n => (discRadialTestRadius n).val) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, discRadialPoint_norm, Complex.UnitDisc.coe_zero, norm_zero] using ht
  obtain ⟨n, hsmall, hmem⟩ := ((htr.eventually (gt_mem_nhds r.property.1)).and
    ((tendsto_discRadialTestPoint u).eventually hN)).exists
  exact ⟨discRadialTestRadius n, discRadialPoint_mem_of_le hS h0 hsmall.le u hr, hmem⟩


/-- Genuine angular coordinates pull the actual direction-circle Haar measure to radians modulo2π. -/
def polygonAngleCircleMeasure : Measure (AddCircle (2 * Real.pi)) :=
  polygonDirectionMeasure.map AddCircle.homeomorphCircle'.symm

instance polygonAngleCircleMeasure_isAddLeftInvariant : IsAddLeftInvariant polygonAngleCircleMeasure where
  map_add_left_eq_self a := by
    let e := AddCircle.homeomorphCircle'
    have ht : (fun b : AddCircle (2 * Real.pi) => a + b) ∘ e.symm =
        e.symm ∘ (fun u : Circle => e a * u) := by
      funext u
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      have hadd (p q : AddCircle (2 * Real.pi)) : e (p + q) = e p * e q := by
        induction p using QuotientAddGroup.induction_on
        induction q using QuotientAddGroup.induction_on
        rename_i p q
        rw [← AddCircle.coe_add]
        simp only [e, AddCircle.homeomorphCircle'_apply_mk, Circle.exp_add]
      rw [hadd, e.apply_symm_apply]
    change (polygonDirectionMeasure.map e.symm).map (fun b => a + b) = polygonDirectionMeasure.map e.symm
    have hca : Measurable (fun b : AddCircle (2 * Real.pi) => a + b) :=
      (continuous_const.add continuous_id).measurable
    have hcu : Measurable (fun u : Circle => e a * u) :=
      (continuous_const.mul continuous_id).measurable
    rw [map_map hca e.symm.measurable, ht, ← map_map e.symm.measurable hcu,
      MeasureTheory.map_mul_left_eq_self]

instance polygonAngleCircleMeasure_isProbability : IsProbabilityMeasure polygonAngleCircleMeasure where
  measure_univ := by
    rw [polygonAngleCircleMeasure, map_apply AddCircle.homeomorphCircle'.symm.measurable MeasurableSet.univ,
      preimage_univ, polygonDirectionMeasure_univ]

instance polygonAngleCircleMeasure_isAddHaar : IsAddHaarMeasure polygonAngleCircleMeasure := by
  let : IsOpenPosMeasure polygonAngleCircleMeasure :=
    AddCircle.homeomorphCircle'.symm.continuous.isOpenPosMeasure_map AddCircle.homeomorphCircle'.symm.surjective
  exact { toIsFiniteMeasureOnCompacts := inferInstance
          toIsAddLeftInvariant := inferInstance
          toIsOpenPosMeasure := inferInstance }

theorem polygonAngleCircleMeasure_eq_scaled_volume :
    polygonAngleCircleMeasure = (ENNReal.ofReal (2 * Real.pi))⁻¹ •
      (volume : Measure (AddCircle (2 * Real.pi))) := by
  let ν : Measure (AddCircle (2 * Real.pi)) := (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume
  have hT : ENNReal.ofReal (2 * Real.pi) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  let : IsAddHaarMeasure ν := IsAddHaarMeasure.smul _
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top) (ENNReal.inv_ne_top.mpr hT)
  let : IsProbabilityMeasure ν := ⟨by
    change ((ENNReal.ofReal (2 * Real.pi))⁻¹ • (volume : Measure (AddCircle (2 * Real.pi)))) univ = 1
    rw [Measure.smul_apply, smul_eq_mul, AddCircle.measure_univ, ENNReal.inv_mul_cancel hT ENNReal.ofReal_ne_top]⟩
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure polygonAngleCircleMeasure ν


/-- Normalized circle Haar measure is exactly ordinary radian arc length divided by2π. -/
theorem polygonDirectionMeasure_closedArc (a : AddCircle (2 * Real.pi)) (r : ℝ) :
    polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc a r) =
      (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (min (2 * Real.pi) (2 * r)) := by
  have he : polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc a r) =
      polygonAngleCircleMeasure (Metric.closedBall a r) := by
    rw [polygonAngleCircleMeasure,
      AddCircle.homeomorphCircle'.symm.measurableEmbedding.map_apply]
    congr 1
    exact (AddCircle.homeomorphCircle'.toEquiv.image_eq_preimage_symm _)
  rw [he, polygonAngleCircleMeasure_eq_scaled_volume, Measure.smul_apply,
    smul_eq_mul, AddCircle.volume_closedBall]

theorem polygonDirectionMeasure_closedArc_radians (a : AddCircle (2 * Real.pi))
    {r : ℝ} (hr : 0 ≤ r) (hrπ : r ≤ Real.pi) :
    2 * Real.pi * (polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc a r)).toReal = 2 * r := by
  rw [polygonDirectionMeasure_closedArc, min_eq_right (by linarith), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  field_simp


/-- A genuine closed angular arc has exactly the existing Euclidean geometric angle between its boundary directions. -/
theorem polygonDirectionMeasure_closedArc_eq_geometric_angle (a : ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hrπ : r ≤ Real.pi / 2) :
    2 * Real.pi * (polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc
      (a : AddCircle (2 * Real.pi)) r)).toReal =
      InnerProductGeometry.angle (Circle.exp (a - r) : ℂ) (Circle.exp (a + r) : ℂ) := by
  rw [polygonDirectionMeasure_closedArc_radians _ hr (by linarith), _root_.LowDimensionalTopology.Geometry.Euclidean.circle_exp_endpoint_angle _ hr hrπ]

/-- The genuine closed Euclidean radial sector in the original disc, including its vertex. -/
def discClosedAngularSector (a : AddCircle (2 * Real.pi)) (r : ℝ) : Set Complex.UnitDisc :=
  {z | z = 0 ∨ ∃ (s : Ioo (0 : ℝ) 1) (u : Circle),
    u ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc a r ∧ z = discRadialPoint s u}

theorem discRadialPoint_eq_iff (r s : Ioo (0 : ℝ) 1) (u v : Circle) :
    discRadialPoint r u = discRadialPoint s v ↔ r = s ∧ u = v := by
  constructor
  · intro h
    have hrs : r.val = s.val := by
      have hn := congrArg (fun z : Complex.UnitDisc => ‖(z : ℂ)‖) h
      simpa only [discRadialPoint_norm] using hn
    have he : r = s := Subtype.ext hrs
    subst s
    refine ⟨rfl, ?_⟩
    apply Subtype.ext
    have hmul := congrArg (fun z : Complex.UnitDisc => (z : ℂ)) h
    change (r.val : ℂ) * (u : ℂ) = (r.val : ℂ) * (v : ℂ) at hmul
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr r.property.1.ne') hmul
  · rintro ⟨rfl, rfl⟩; rfl

theorem discRadialDirections_closedAngularSector (a : AddCircle (2 * Real.pi)) (r : ℝ) :
    discRadialDirections (discClosedAngularSector a r) = _root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc a r := by
  ext u
  constructor
  · rintro ⟨s, hz | ⟨t, v, hv, he⟩⟩
    · have hn := congrArg (fun z : Complex.UnitDisc => ‖(z : ℂ)‖) hz
      have : s.val = 0 := by simpa only [discRadialPoint_norm, Complex.UnitDisc.coe_zero, norm_zero] using hn
      exact (s.property.1.ne' this).elim
    · have huv := ((discRadialPoint_eq_iff s t u v).mp he).2
      exact huv.symm ▸ hv
  · intro hu
    exact ⟨discRadialTestRadius 0, Or.inr ⟨discRadialTestRadius 0, u, hu, rfl⟩⟩

theorem discSubtendedAngularFraction_zero (S : Set Complex.UnitDisc) :
    discSubtendedAngularFraction S 0 = polygonDirectionMeasure (discRadialDirections S) :=
  polygonDirectionMeasure_radial_isometry (discOriginNormalizer 0) (discOriginNormalizer_isometry 0)
    (discOriginNormalizer_apply_self 0) S

/-- A genuine disc sector's subtended angle is exactly the pre-existing Mathlib angle between its actual boundary rays. -/
theorem discSubtendedAngle_closedAngularSector (a : ℝ) {r : ℝ} (hr : 0 ≤ r) (hrπ : r ≤ Real.pi / 2) :
    discSubtendedAngle (discClosedAngularSector (a : AddCircle (2 * Real.pi)) r) 0 =
      InnerProductGeometry.angle (Circle.exp (a - r) : ℂ) (Circle.exp (a + r) : ℂ) := by
  rw [discSubtendedAngle, discSubtendedAngularFraction_zero, discRadialDirections_closedAngularSector]
  exact polygonDirectionMeasure_closedArc_eq_geometric_angle a hr hrπ

theorem polygonClosedDirectionArc_semicircle :
    _root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc 0 (Real.pi / 2) = {u : Circle | 0 ≤ (u : ℂ).re} := by
  ext u
  change u ∈ AddCircle.homeomorphCircle' '' Metric.closedBall 0 (Real.pi / 2) ↔ _
  have him : AddCircle.homeomorphCircle' '' Metric.closedBall (0 : AddCircle (2 * Real.pi)) (Real.pi / 2) =
      AddCircle.homeomorphCircle'.symm ⁻¹' Metric.closedBall 0 (Real.pi / 2) :=
    AddCircle.homeomorphCircle'.toEquiv.image_eq_preimage_symm _
  rw [him]
  change dist (AddCircle.homeomorphCircle'.symm u) 0 ≤ Real.pi / 2 ↔ _
  have he : AddCircle.homeomorphCircle'.symm u = (Complex.arg (u : ℂ) : AddCircle (2 * Real.pi)) := by
    rw [AddCircle.homeomorphCircle'_symm_apply]
  rw [dist_zero_right, he]
  have hn : ‖(Complex.arg (u : ℂ) : AddCircle (2 * Real.pi))‖ = |Complex.arg (u : ℂ)| :=
    (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr (by
      rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      convert Complex.abs_arg_le_pi (u : ℂ) using 1; ring)
  rw [hn]
  exact Complex.abs_arg_le_pi_div_two_iff

theorem exists_discRadialPoint_representation (z : Complex.UnitDisc) (hz : z ≠ 0) :
    ∃ (r : Ioo (0 : ℝ) 1) (u : Circle), z = discRadialPoint r u := by
  have hzC : (z : ℂ) ≠ 0 := by intro he; exact hz (Complex.UnitDisc.coe_injective (by simpa using he))
  have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hzC
  let r : Ioo (0 : ℝ) 1 := ⟨‖(z : ℂ)‖, hn, z.norm_lt_one⟩
  let u : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    change (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, div_self hn.ne']⟩
  refine ⟨r, u, ?_⟩
  apply Complex.UnitDisc.coe_injective
  change (z : ℂ) = (‖(z : ℂ)‖ : ℂ) * ((z : ℂ) / (‖(z : ℂ)‖ : ℂ))
  exact (mul_div_cancel₀ (z : ℂ) (Complex.ofReal_ne_zero.mpr hn.ne')).symm

/-- This genuine sector is exactly the ordinary Euclidean closed half-disc. -/
theorem discClosedAngularSector_semicircle :
    discClosedAngularSector 0 (Real.pi / 2) = {z : Complex.UnitDisc | 0 ≤ (z : ℂ).re} := by
  ext z
  constructor
  · rintro (rfl | ⟨r, u, hu, rfl⟩)
    · simp
    · rw [polygonClosedDirectionArc_semicircle] at hu
      change 0 ≤ ((r.val : ℂ) * (u : ℂ)).re
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        mul_nonneg r.property.1.le hu
  · intro hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · obtain ⟨r, u, rfl⟩ := exists_discRadialPoint_representation z hz0
      refine Or.inr ⟨r, u, ?_, rfl⟩
      rw [polygonClosedDirectionArc_semicircle]
      change 0 ≤ (u : ℂ).re
      change 0 ≤ ((r.val : ℂ) * (u : ℂ)).re at hz
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hz
      exact nonneg_of_mul_nonneg_right hz r.property.1

/-- An actual straight side has the ordinary angleπ in the literal native closed half-disc model. -/
theorem discSubtendedAngle_closedHalfDisc :
    discSubtendedAngle {z : Complex.UnitDisc | 0 ≤ (z : ℂ).re} 0 = Real.pi := by
  rw [← discClosedAngularSector_semicircle, discSubtendedAngle, discSubtendedAngularFraction_zero,
    discRadialDirections_closedAngularSector,
    polygonDirectionMeasure_closedArc_radians 0 (by positivity) (by linarith [Real.pi_pos])]
  ring

theorem hyperbolicDirection_I_cayley (w : ℍ) :
    hyperbolicDirection UpperHalfPlane.I w =
      Complex.normSq ((w : ℂ) + Complex.I) • (Complex.I * (halfPlaneToDisc w : ℂ)) := by
  have hd : Complex.normSq ((w : ℂ) + Complex.I) ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (cayley_denom_ne_zero w))
  apply Complex.ext
  all_goals
    simp only [hyperbolicDirection, UpperHalfPlane.I_re, UpperHalfPlane.I_im,
      halfPlaneToDisc, Complex.UnitDisc.coe_mk, cayleyFormula, Complex.smul_re, Complex.smul_im,
      smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      Complex.normSq_apply, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero]
    field_simp
    ring

/-- The existing genuine forward-tangent HRay angle atI is exactly the Euclidean angle of the actual Cayley radial directions. -/
theorem hInteriorAngleMeasure_I_cayley {w u : ℍ} (R S : HRayAt UpperHalfPlane.I)
    (hw : w ∈ R.val) (hwI : w ≠ UpperHalfPlane.I)
    (hu : u ∈ S.val) (huI : u ≠ UpperHalfPlane.I) :
    hInteriorAngleMeasure R S =
      InnerProductGeometry.angle (halfPlaneToDisc w : ℂ) (halfPlaneToDisc u : ℂ) := by
  have hwpos : 0 < Complex.normSq ((w : ℂ) + Complex.I) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (cayley_denom_ne_zero w))
  have hupos : 0 < Complex.normSq ((u : ℂ) + Complex.I) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (cayley_denom_ne_zero u))
  rw [hInteriorAngleMeasure_eq_direction R S hw hwI hu huI,
    hyperbolicDirection_I_cayley, hyperbolicDirection_I_cayley,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hwpos,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hupos,
    Complex.angle_mul_left Complex.I_ne_zero]

theorem discToHalfPlane_radialPoint_ne_I (r : Ioo (0 : ℝ) 1) (u : Circle) :
    discToHalfPlane (discRadialPoint r u) ≠ UpperHalfPlane.I := by
  intro he
  have hz := congrArg halfPlaneToDisc he
  rw [halfPlaneToDisc_discToHalfPlane] at hz
  have hz0 : halfPlaneToDisc UpperHalfPlane.I = 0 := by
    simpa only [discToHalfPlane_zero] using halfPlaneToDisc_discToHalfPlane (0 : Complex.UnitDisc)
  rw [hz0] at hz
  have hn := congrArg (fun z : Complex.UnitDisc => ‖(z : ℂ)‖) hz
  have hr0 : r.val = 0 := by
    simpa only [discRadialPoint_norm, Complex.UnitDisc.coe_zero, norm_zero] using hn
  exact r.property.1.ne' hr0

/-- The sector bridge uses the same genuine forward-tangent HRay angle already formalized. -/
theorem discSubtendedAngle_closedSector_eq_HRay (a : ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hrπ : r ≤ Real.pi / 2) (R S : HRayAt UpperHalfPlane.I)
    (hR : discToHalfPlane (discRadialPoint (discRadialTestRadius 0) (Circle.exp (a - r))) ∈ R.val)
    (hS : discToHalfPlane (discRadialPoint (discRadialTestRadius 0) (Circle.exp (a + r))) ∈ S.val) :
    discSubtendedAngle (discClosedAngularSector (a : AddCircle (2 * Real.pi)) r) 0 =
      hInteriorAngleMeasure R S := by
  rw [discSubtendedAngle_closedAngularSector a hr hrπ,
    hInteriorAngleMeasure_I_cayley R S hR (discToHalfPlane_radialPoint_ne_I _ _)
      hS (discToHalfPlane_radialPoint_ne_I _ _),
    halfPlaneToDisc_discToHalfPlane, halfPlaneToDisc_discToHalfPlane]
  change InnerProductGeometry.angle (Circle.exp (a - r) : ℂ) (Circle.exp (a + r) : ℂ) =
    InnerProductGeometry.angle
      ((discRadialTestRadius 0).val • (Circle.exp (a - r) : ℂ))
      ((discRadialTestRadius 0).val • (Circle.exp (a + r) : ℂ))
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (discRadialTestRadius 0).property.1,
    InnerProductGeometry.angle_smul_right_of_pos _ _ (discRadialTestRadius 0).property.1]

end LowDimensionalTopology.Geometry.Hyperbolic
