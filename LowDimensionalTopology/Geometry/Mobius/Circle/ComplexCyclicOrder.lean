module
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexCircles

/-!
# Geometric circle order and the positive cross-ratio range

Cyclic order is expressed by strict Euclidean separation across
a diagonal in a finite circle chart. Signed-area determinants, rather than
cross-ratio values, define the geometric side condition. The finite predicate
is proved to lie on a genuine positive-radius circle, and the extended
predicate is invariant under the actual Möbius group.
-/

@[expose] public section
noncomputable section
open scoped OnePoint RealInnerProductSpace ComplexConjugate
namespace LowDimensionalTopology.Geometry.Mobius

/-- Coordinates transverse to the Euclidean diagonal ac have opposite signs at b and d. -/
def ComplexDiagonalSeparates (a b c d : ℂ) : Prop :=
  (((b - a) / (c - a)).im * ((d - a) / (c - a)).im) < 0

/-- The ordinary signed area determinant relative to an oriented Euclidean line. -/
def complexDiagonalSide (a c z : ℂ) : ℝ :=
  (c - a).re * (z - a).im - (c - a).im * (z - a).re

/-- Diagonal coordinates have the same sign as the genuine oriented area, with a positive squared-length divisor. -/
theorem complexDiagonalSide_division (a c z : ℂ) :
    ((z - a) / (c - a)).im = complexDiagonalSide a c z / Complex.normSq (c - a) := by
  rw [Complex.div_im]
  unfold complexDiagonalSide
  ring

/-- The separation predicate is precisely that b and d lie on strictly opposite Euclidean sides of the diagonal ac. -/
theorem complexDiagonalSeparates_iff_sides (a b c d : ℂ) (hca : c ≠ a) :
    ComplexDiagonalSeparates a b c d ↔ complexDiagonalSide a c b * complexDiagonalSide a c d < 0 := by
  have hn : 0 < Complex.normSq (c - a) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hca)
  unfold ComplexDiagonalSeparates
  rw [complexDiagonalSide_division, complexDiagonalSide_division, div_mul_div_comm,
    div_lt_iff₀ (mul_pos hn hn), zero_mul]

/-- The normalized complex ratio, in the chart with first and third points zero and one. -/
theorem crossRatio_zero_third_one (p q : ℂ) :
    extendedCrossRatio (0 : ℂ) p (1 : ℂ) q = (p - q) / (p * (1 - q)) := by
  rw [extendedCrossRatio_coe]
  simp
  rw [show q - p = -(p - q) by ring, neg_div_neg_eq]

/-- A reciprocal identity retaining the real ratio as an independent scalar. -/
theorem crossRatio_reciprocal_identity (p q : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) (hq1 : q ≠ 1) :
    (extendedCrossRatio (0 : ℂ) p (1 : ℂ) q - 1) * (1 / q) =
      extendedCrossRatio (0 : ℂ) p (1 : ℂ) q - 1 / p := by
  rw [crossRatio_zero_third_one]
  field_simp [hp, hq, sub_ne_zero.mpr (Ne.symm hq1)]
  ring

/-- Opposite geometric sides of the zero-to-one diagonal force a real ratio to exceed one. -/
theorem crossRatio_gt_one_of_normalized_sides (p q : ℂ)
    (hside : p.im * q.im < 0) (hq1 : q ≠ 1)
    (hreal : (extendedCrossRatio (0 : ℂ) p (1 : ℂ) q).im = 0) :
    1 < (extendedCrossRatio (0 : ℂ) p (1 : ℂ) q).re := by
  have hp : p ≠ 0 := by intro h; simp [h] at hside
  have hq : q ≠ 0 := by intro h; simp [h] at hside
  have hpn : 0 < Complex.normSq p := Complex.normSq_pos.mpr hp
  have hqn : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hi := congrArg Complex.im (crossRatio_reciprocal_identity p q hp hq hq1)
  simp only [one_div, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, hreal, zero_sub, zero_mul, sub_zero, add_zero,
    Complex.inv_im] at hi
  field_simp [hpn.ne', hqn.ne'] at hi
  have hm := congrArg (fun x : ℝ => x * q.im) hi
  have hneg : p.im * q.im * Complex.normSq q < 0 := mul_neg_of_neg_of_pos hside hqn
  have hpos : 0 < ((extendedCrossRatio (0 : ℂ) p (1 : ℂ) q).re - 1) *
      (q.im ^ 2 * Complex.normSq p) := by nlinarith
  have hf : 0 ≤ q.im ^ 2 * Complex.normSq p := mul_nonneg (sq_nonneg _) hpn.le
  nlinarith

/-- The Euclidean similarity sending the first diagonal endpoint to zero and the second to one. -/
def complexDiagonalNormalizer (a c : ℂ) (hca : c ≠ a) : complexMobiusGroup :=
  mobiusMatrixProjection (coefficientMatrix 1 (-a) 0 (c - a) (by simpa using sub_ne_zero.mpr hca))

theorem complexDiagonalNormalizer_coe (a c z : ℂ) (hca : c ≠ a) :
    (complexDiagonalNormalizer a c hca : Equiv.Perm ExtendedComplex) z =
      (((z - a) / (c - a) : ℂ) : ExtendedComplex) := by
  change fractionalLinearOfCoefficients 1 (-a) 0 (c - a) _ z = _
  rw [fractionalLinearOfCoefficients_affine]
  simp [sub_eq_add_neg]

/-- Real Euclidean inner products in complex coordinates. -/
theorem cyclicOrder_real_inner_coordinates (z w : ℂ) :
    inner ℝ z w = z.re * w.re + z.im * w.im := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  change (conj z * w).re = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Three points of a genuine Euclidean line have zero signed diagonal area. -/
theorem complexDiagonalSide_zero_of_line (a b c n : ℂ) (t : ℝ) (hn : n ≠ 0)
    (ha : inner ℝ a n = t) (hb : inner ℝ b n = t) (hc : inner ℝ c n = t) :
    complexDiagonalSide a c b = 0 := by
  have hB : (b-a).re * n.re + (b-a).im * n.im = 0 := by
    rw [← cyclicOrder_real_inner_coordinates, inner_sub_left, hb, ha, sub_self]
  have hC : (c-a).re * n.re + (c-a).im * n.im = 0 := by
    rw [← cyclicOrder_real_inner_coordinates, inner_sub_left, hc, ha, sub_self]
  have he : complexDiagonalSide a c b * Complex.normSq n =
      ((b-a).re*n.re+(b-a).im*n.im) * ((c-a).re*n.im-(c-a).im*n.re) -
      ((c-a).re*n.re+(c-a).im*n.im) * ((b-a).re*n.im-(b-a).im*n.re) := by
    simp only [complexDiagonalSide, Complex.normSq_apply]
    ring
  rw [hB, hC, zero_mul, zero_mul, sub_self] at he
  exact (mul_eq_zero.mp he).resolve_right (Complex.normSq_pos.mpr hn).ne'

/-- Finite cyclic order is expressed by a genuine circle and strict separation by its diagonal, independently of the ratio. -/
def FiniteComplexCyclicOrder (a b c d : ℂ) : Prop :=
  ComplexConcyclic a b c d ∧ ComplexDiagonalSeparates a b c d

/-- Strict diagonal separation rules out a line: the finite order predicate lies on a genuine positive-radius circle. -/
theorem FiniteComplexCyclicOrder.exists_circle {a b c d : ℂ} (h : FiniteComplexCyclicOrder a b c d) :
    ∃ center : ℂ, ∃ radius : ℝ, 0 < radius ∧
      ‖a-center‖=radius ∧ ‖b-center‖=radius ∧ ‖c-center‖=radius ∧ ‖d-center‖=radius := by
  obtain ⟨_, S, hS, ha, hb, hc, hd⟩ := h.1
  rcases (isComplexGeneralizedCircle_iff S).mp hS with ⟨center,radius,hr,he⟩ | ⟨normal,t,hn,he⟩
  · exact ⟨center,radius,hr, (complexCircle_coe _ _ _).mp (he ▸ ha),
      (complexCircle_coe _ _ _).mp (he ▸ hb), (complexCircle_coe _ _ _).mp (he ▸ hc),
      (complexCircle_coe _ _ _).mp (he ▸ hd)⟩
  · have hca : c ≠ a := by intro hz; exact h.1.1.2.1 (by rw [hz])
    have hs := (complexDiagonalSeparates_iff_sides a b c d hca).mp h.2
    have hzero := complexDiagonalSide_zero_of_line a b c normal t hn
      ((complexLine_coe _ _ _).mp (he ▸ ha)) ((complexLine_coe _ _ _).mp (he ▸ hb))
      ((complexLine_coe _ _ _).mp (he ▸ hc))
    rw [hzero, zero_mul] at hs
    exact (lt_irrefl _ hs).elim

theorem crossRatio_gt_one_of_finite_cyclicOrder (a b c d : ℂ) (h : FiniteComplexCyclicOrder a b c d) :
    1 < (extendedCrossRatio a b c d).re := by
  have hd := h.1.1
  have hca : c ≠ a := by
    intro he
    exact hd.2.1 (by rw [he])
  let f := complexDiagonalNormalizer a c hca
  let p := (b - a) / (c - a)
  let q := (d - a) / (c - a)
  have hnorm : extendedCrossRatio (0 : ℂ) p (1 : ℂ) q = extendedCrossRatio a b c d := by
    have hi := extendedCrossRatio_mobius f a b c d
    simp only [f, complexDiagonalNormalizer_coe, sub_self, zero_div, div_self (sub_ne_zero.mpr hca)] at hi
    exact hi
  have hreal : (extendedCrossRatio (0 : ℂ) p (1 : ℂ) q).im = 0 := by
    rw [hnorm]
    exact (complexConcyclic_iff_crossRatio_real a b c d hd).mp h.1
  have hq1 : q ≠ 1 := by
    intro he
    have hs := h.2
    change p.im * q.im < 0 at hs
    rw [he, Complex.one_im, mul_zero] at hs
    exact lt_irrefl _ hs
  rw [← hnorm]
  exact crossRatio_gt_one_of_normalized_sides p q h.2 hq1 hreal

/-- Unoriented cyclic order on a generalized circle, using strict diagonal-side separation in a finite geometric chart. -/
def ComplexCyclicOrder (a b c d : ExtendedComplex) : Prop :=
  ∃ f : complexMobiusGroup, ∃ A B C D : ℂ,
    (f : Equiv.Perm ExtendedComplex) a = A ∧ (f : Equiv.Perm ExtendedComplex) b = B ∧
      (f : Equiv.Perm ExtendedComplex) c = C ∧ (f : Equiv.Perm ExtendedComplex) d = D ∧
        FiniteComplexCyclicOrder A B C D

theorem FiniteComplexCyclicOrder.to_extended {a b c d : ℂ} (h : FiniteComplexCyclicOrder a b c d) :
    ComplexCyclicOrder a b c d := ⟨1, a, b, c, d, rfl, rfl, rfl, rfl, h⟩

theorem ComplexCyclicOrder.distinct {a b c d : ExtendedComplex} (h : ComplexCyclicOrder a b c d) :
    QuadrupleDistinct a b c d := by
  obtain ⟨f, A, B, C, D, ha, hb, hc, hd, horder⟩ := h
  obtain ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩ := horder.1.1
  exact ⟨fun he => hAB (ha.symm.trans ((congrArg f.val he).trans hb)),
    fun he => hAC (ha.symm.trans ((congrArg f.val he).trans hc)),
    fun he => hAD (ha.symm.trans ((congrArg f.val he).trans hd)),
    fun he => hBC (hb.symm.trans ((congrArg f.val he).trans hc)),
    fun he => hBD (hb.symm.trans ((congrArg f.val he).trans hd)),
    fun he => hCD (hc.symm.trans ((congrArg f.val he).trans hd))⟩

/-- The geometric circle-order predicate is independent of the chosen complex Möbius chart. -/
theorem ComplexCyclicOrder.image {a b c d : ExtendedComplex} (h : ComplexCyclicOrder a b c d)
    (g : complexMobiusGroup) :
    ComplexCyclicOrder ((g : Equiv.Perm ExtendedComplex) a) ((g : Equiv.Perm ExtendedComplex) b)
      ((g : Equiv.Perm ExtendedComplex) c) ((g : Equiv.Perm ExtendedComplex) d) := by
  obtain ⟨f, A, B, C, D, ha, hb, hc, hd, horder⟩ := h
  refine ⟨f * g⁻¹, A, B, C, D, ?_, ?_, ?_, ?_, horder⟩
  · change f.val (g.val.symm (g.val a)) = A
    rw [g.val.symm_apply_apply]
    exact ha
  · change f.val (g.val.symm (g.val b)) = B
    rw [g.val.symm_apply_apply]
    exact hb
  · change f.val (g.val.symm (g.val c)) = C
    rw [g.val.symm_apply_apply]
    exact hc
  · change f.val (g.val.symm (g.val d)) = D
    rw [g.val.symm_apply_apply]
    exact hd

/-- genuine geometric cyclic order gives a real cross-ratio strictly greater than one. -/
theorem crossRatio_real_gt_one_of_cyclicOrder (a b c d : ExtendedComplex) (h : ComplexCyclicOrder a b c d) :
    (extendedCrossRatio a b c d).im = 0 ∧ 1 < (extendedCrossRatio a b c d).re := by
  obtain ⟨f, A, B, C, D, ha, hb, hc, hd, horder⟩ := h
  have he := extendedCrossRatio_mobius f a b c d
  rw [ha, hb, hc, hd] at he
  rw [← he]
  exact ⟨(complexConcyclic_iff_crossRatio_real A B C D horder.1.1).mp horder.1,
    crossRatio_gt_one_of_finite_cyclicOrder A B C D horder⟩

/-- Actual complex Möbius maps preserve the geometric four-point circle condition. -/
theorem ComplexConcyclic.image {a b c d : ExtendedComplex} (h : ComplexConcyclic a b c d)
    (f : complexMobiusGroup) :
    ComplexConcyclic (f.val a) (f.val b) (f.val c) (f.val d) := by
  obtain ⟨hd, S, hS, ha, hb, hc, hdS⟩ := h
  have hi := f.val.injective
  exact ⟨⟨hi.ne hd.1, hi.ne hd.2.1, hi.ne hd.2.2.1, hi.ne hd.2.2.2.1,
    hi.ne hd.2.2.2.2.1, hi.ne hd.2.2.2.2.2⟩, f.val '' S, hS.image f.property.1,
    ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩, ⟨d, hdS, rfl⟩⟩

/-- A circle chart with its pole away from the whole extended real axis. -/
def cyclicCircleMap : complexMobiusGroup :=
  mobiusMatrixProjection (coefficientMatrix 1 (-Complex.I) 1 Complex.I
    (by intro h; have hi := congrArg Complex.im h; norm_num at hi))

theorem cyclicCircleMap_coe (z : ℂ) (hz : z + Complex.I ≠ 0) :
    cyclicCircleMap.val z = (((z - Complex.I) / (z + Complex.I) : ℂ) : ExtendedComplex) := by
  change fractionalLinearOfCoefficients 1 (-Complex.I) 1 Complex.I _ z = _
  rw [fractionalLinearOfCoefficients_finite _ _ _ _ _ _ (by simpa using hz)]
  simp [sub_eq_add_neg]

theorem cyclicCircleMap_zero : cyclicCircleMap.val (0 : ℂ) = ((-1 : ℂ) : ExtendedComplex) := by
  rw [cyclicCircleMap_coe 0 (by simp)]
  simp

theorem cyclicCircleMap_one : cyclicCircleMap.val (1 : ℂ) = ((-Complex.I : ℂ) : ExtendedComplex) := by
  have hd : (1 : ℂ) + Complex.I ≠ 0 := by intro h; have hi := congrArg Complex.re h; norm_num at hi
  rw [cyclicCircleMap_coe 1 hd]
  apply congrArg (fun z : ℂ => (z : ExtendedComplex))
  apply (div_eq_iff hd).mpr
  simp [mul_add]
  ring

theorem cyclicCircleMap_infty : cyclicCircleMap.val ∞ = ((1 : ℂ) : ExtendedComplex) := by
  change fractionalLinearOfCoefficients 1 (-Complex.I) 1 Complex.I _ ∞ = _
  rw [fractionalLinearOfCoefficients_infty]
  simp

/-- Explicit diagonal coordinates for four genuine circle points, without angles or ratio-valued order definitions. -/
theorem cyclicCircleMap_diagonal_coordinates (x : ℝ) (hx : 1 < x) :
    (((-Complex.I : ℂ) - (-1)) / (((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I) - (-1))) =
      ((1 - Complex.I) * ((x : ℂ) + Complex.I) / (2*x)) ∧
    (((1 : ℂ) - (-1)) / (((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I) - (-1))) =
      (1 + Complex.I / x) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hd : (x : ℂ) + Complex.I ≠ 0 := by intro h; have hi := congrArg Complex.im h; norm_num at hi
  have hC : ((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I) - (-1) ≠ 0 := by
    have he : ((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I) - (-1) = 2*x/((x : ℂ)+Complex.I) := by
      field_simp
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) hd
  constructor
  · field_simp [hd, hx0, hC]
    ring_nf
    simp [hx0]
    ring
  · field_simp [hd, hx0, hC]
    ring_nf
    simp [hx0]

theorem cyclicCircleMap_strict_sides (x : ℝ) (hx : 1 < x) :
    ComplexDiagonalSeparates (-1) (-Complex.I) (((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I)) 1 := by
  have hcoord := cyclicCircleMap_diagonal_coordinates x hx
  unfold ComplexDiagonalSeparates
  rw [hcoord.1, hcoord.2]
  have him : (((1 - Complex.I) * ((x : ℂ) + Complex.I) / (2*x) : ℂ)).im = (1-x)/(2*x) := by
    rw [show (2 * (x : ℂ)) = ((2*x : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_im]
    simp [Complex.mul_im, sub_eq_add_neg]
  rw [him]
  simp only [Complex.add_im, Complex.one_im, Complex.div_ofReal_im, Complex.I_im, zero_add]
  have hx0 : 0 < x := by linarith
  have hfirst : (1 - x) / (2 * x) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hsecond : 0 < (1 : ℝ) / x := one_div_pos.mpr hx0
  exact mul_neg_of_neg_of_pos hfirst hsecond

/-- Every real ratio above one has the genuine diagonal-separated circle order, including source configurations containing infinity. -/
theorem complexCyclicOrder_of_crossRatio_real_gt_one (a b c d : ExtendedComplex)
    (hd : QuadrupleDistinct a b c d) (hreal : (extendedCrossRatio a b c d).im = 0)
    (hgt : 1 < (extendedCrossRatio a b c d).re) : ComplexCyclicOrder a b c d := by
  obtain ⟨q, h0, h1, hi⟩ := mobius_normalize_triple a b d ⟨hd.1, hd.2.2.1, hd.2.2.2.2.1⟩
  have hratio := mobius_normalized_crossRatio q a b c d h0 h1 hi hd.2.2.2.2.2
  let x := (extendedCrossRatio a b c d).re
  have hx : 1 < x := hgt
  have hratioReal : (x : ℂ) = extendedCrossRatio a b c d := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hreal.symm
  have hxden : (x : ℂ) + Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    norm_num at hh
  let f := cyclicCircleMap * q
  have ha : f.val a = ((-1 : ℂ) : ExtendedComplex) := by
    change cyclicCircleMap.val (q.val a) = _
    rw [h0, cyclicCircleMap_zero]
  have hb : f.val b = ((-Complex.I : ℂ) : ExtendedComplex) := by
    change cyclicCircleMap.val (q.val b) = _
    rw [h1, cyclicCircleMap_one]
  have hc : f.val c = ((((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I) : ℂ) : ExtendedComplex) := by
    change cyclicCircleMap.val (q.val c) = _
    rw [← hratio, ← hratioReal, cyclicCircleMap_coe x hxden]
  have hd' : f.val d = ((1 : ℂ) : ExtendedComplex) := by
    change cyclicCircleMap.val (q.val d) = _
    rw [hi, cyclicCircleMap_infty]
  have hcon := ((complexConcyclic_iff_crossRatio_real a b c d hd).mpr hreal).image f
  rw [ha, hb, hc, hd'] at hcon
  exact ⟨f, -1, -Complex.I, ((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I), 1,
    ha, hb, hc, hd', hcon, cyclicCircleMap_strict_sides x hx⟩

/-- The geometric order predicate covers exactly the real greater-than-one range, rather than just a chosen subset of circle configurations. -/
theorem complexCyclicOrder_iff_crossRatio_real_gt_one (a b c d : ExtendedComplex)
    (hd : QuadrupleDistinct a b c d) :
    ComplexCyclicOrder a b c d ↔
      (extendedCrossRatio a b c d).im = 0 ∧ 1 < (extendedCrossRatio a b c d).re :=
  ⟨crossRatio_real_gt_one_of_cyclicOrder a b c d,
    fun h => complexCyclicOrder_of_crossRatio_real_gt_one a b c d hd h.1 h.2⟩

theorem ComplexCyclicOrder.concyclic {a b c d : ExtendedComplex} (h : ComplexCyclicOrder a b c d) :
    ComplexConcyclic a b c d :=
  (complexConcyclic_iff_crossRatio_real a b c d h.distinct).mpr
    (crossRatio_real_gt_one_of_cyclicOrder a b c d h).1

end LowDimensionalTopology.Geometry.Mobius
