module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexCircles
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.MobiusTriples
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import LowDimensionalTopology.Geometry.Mobius.ReflectionEquivalence
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Geometric discs bounded by generalized circles.

A geometric disc is a connected component of the complement of a generalized circle.
Möbius transformations normalize these discs to the unit disc; the components are open
and connected.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Function Filter Metric
open scoped OnePoint ComplexConjugate Pointwise RealInnerProductSpace Topology

namespace LowDimensionalTopology.Geometry.Mobius

theorem isConnected_extendedUnitDisc : IsConnected Hyperbolic.extendedUnitDisc := by
  have hc : IsConnected (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).isConnected ⟨0, by simp⟩
  have h : IsConnected {z : ℂ | ‖z‖ < 1} := by simpa only [ball, dist_zero_right] using hc
  exact h.image (OnePoint.some : ℂ → ExtendedComplex) OnePoint.continuous_coe.continuousOn

theorem isOpen_extendedUnitDisc : IsOpen Hyperbolic.extendedUnitDisc := by
  apply OnePoint.isOpen_image_coe.mpr
  exact isOpen_lt continuous_norm continuous_const

/-- The genuine exterior of the closed unit disc in the one-point compactification. -/
def extendedUnitDiscExterior : Set ExtendedComplex := Hyperbolic.extendedClosedUnitDiscᶜ

theorem reciprocal_involutive : Function.Involutive (reciprocal : ExtendedComplex → ExtendedComplex) := by
  intro z
  induction z using OnePoint.rec with
  | infty => rw [reciprocal_infty, reciprocal_zero]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      rw [reciprocal_zero, reciprocal_infty]
    · rw [reciprocal_coe z hz, reciprocal_coe z⁻¹ (inv_ne_zero hz), inv_inv]

theorem infty_not_mem_extendedUnitDisc : ∞ ∉ Hyperbolic.extendedUnitDisc := by
  simp [Hyperbolic.extendedUnitDisc]

/-- The reciprocal boundary map bundled in the actual Mobius group. -/
def reciprocalMobius : complexMobiusGroup :=
  mobiusMatrixProjection (coefficientMatrix 0 1 1 0 (by norm_num))

/-- A positive-radius geometric disc or half-plane is an open complementary component of a genuine circle. -/
def IsComplexOpenDisc (D : Set ExtendedComplex) : Prop :=
  ∃ S : Set ExtendedComplex, IsComplexGeneralizedCircle S ∧
    ∃ z ∈ Sᶜ, D = connectedComponentIn Sᶜ z

/-- Every genuine generalized circle has an ordered triple of distinct points. -/
theorem IsComplexGeneralizedCircle.exists_triple {S : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) :
    ∃ a b c : ExtendedComplex, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ TripleDistinct a b c := by
  rcases (isComplexGeneralizedCircle_iff S).mp hS with
    ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · refine ⟨((c + (r : ℂ) : ℂ) : ExtendedComplex),
      ((c - (r : ℂ) : ℂ) : ExtendedComplex),
      ((c + Complex.I * (r : ℂ) : ℂ) : ExtendedComplex), ?_, ?_, ?_, ?_⟩
    · rw [complexCircle_coe]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    · rw [complexCircle_coe]
      have h : c - (r : ℂ) - c = -(r : ℂ) := by ring
      rw [h, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    · rw [complexCircle_coe, add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    · constructor
      · intro h
        have he := congrArg Complex.re (OnePoint.coe_injective h)
        simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at he
        linarith
      · constructor
        · intro h
          have he := congrArg Complex.im (OnePoint.coe_injective h)
          simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at he
          linarith
        · intro h
          have he := congrArg Complex.im (OnePoint.coe_injective h)
          simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
            zero_add, sub_zero] at he
          linarith
  · let x : ℂ := (t / ‖a‖ ^ 2) • a
    have hx : inner ℝ x a = t := by
      simp only [x, real_inner_smul_left, real_inner_self_eq_norm_sq]
      exact div_mul_cancel₀ t (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha))
    have hp : inner ℝ (Complex.I * a) a = 0 := by
      simp [Complex.inner, Complex.mul_re, Complex.mul_im]
      ring
    refine ⟨(x : ExtendedComplex), ((x + Complex.I * a : ℂ) : ExtendedComplex), ∞,
      ?_, ?_, complexLine_infty a t, ?_⟩
    · exact (complexLine_coe a x t).mpr hx
    · rw [complexLine_coe, inner_add_left, hx, hp, add_zero]
    · refine ⟨?_, OnePoint.coe_ne_infty _, OnePoint.coe_ne_infty _⟩
      intro h
      have he := OnePoint.coe_injective h
      have hz : Complex.I * a = 0 := by linear_combination -he
      exact ha ((mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero)

/-- The action of an actual Möbius transformation on the boundary is continuous. -/
theorem continuous_mobiusBoundary (f : complexMobiusGroup) :
    Continuous (f : Equiv.Perm ExtendedComplex) := by
  obtain ⟨A, rfl⟩ := mobiusMatrixProjection_surjective f
  exact continuous_fractionalLinear A

theorem disjoint_extendedUnitDisc_exterior : Disjoint Hyperbolic.extendedUnitDisc extendedUnitDiscExterior := by
  rw [Set.disjoint_left]
  intro z hz hi
  exact hi (Hyperbolic.extendedUnitDisc_subset_closed hz)

theorem isOpen_extendedUnitDiscExterior : IsOpen extendedUnitDiscExterior :=
  Hyperbolic.isClosed_extendedClosedUnitDisc.isOpen_compl

theorem infty_mem_extendedUnitDiscExterior : ∞ ∈ extendedUnitDiscExterior := by
  simp [extendedUnitDiscExterior, Hyperbolic.extendedClosedUnitDisc]

theorem coe_mem_extendedUnitDiscExterior (z : ℂ) :
    (z : ExtendedComplex) ∈ extendedUnitDiscExterior ↔ 1 < ‖z‖ := by
  simp only [extendedUnitDiscExterior, mem_compl_iff, Hyperbolic.coe_mem_extendedClosedUnitDisc, not_le]

@[simp] theorem reciprocalMobius_coe : (reciprocalMobius : Equiv.Perm ExtendedComplex) = reciprocal := rfl

/-- The three-point normalization sends any genuine generalized circle to the extended real axis. -/
theorem IsComplexGeneralizedCircle.normalize_to_realAxis {S : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) :
    ∃ q : complexMobiusGroup, (q : Equiv.Perm ExtendedComplex) '' S = complexRealAxis := by
  obtain ⟨a, b, c, ha, hb, hc, hd⟩ := hS.exists_triple
  obtain ⟨q, h0, h1, hi⟩ := mobius_normalize_triple a b c hd
  exact ⟨q, complexCircle_through_zero_one_infty (hS.image q.property.1)
    ⟨a, ha, h0⟩ ⟨b, hb, h1⟩ ⟨c, hc, hi⟩⟩

/-- The actual boundary action, bundled with its proved inverse continuity. -/
def mobiusBoundaryHomeomorph (f : complexMobiusGroup) : ExtendedComplex ≃ₜ ExtendedComplex where
  toEquiv := f.val
  continuous_toFun := continuous_mobiusBoundary f
  continuous_invFun := continuous_mobiusBoundary f⁻¹

theorem unitCircle_compl_eq_disc_union_exterior :
    (complexCircle 0 1)ᶜ = Hyperbolic.extendedUnitDisc ∪ extendedUnitDiscExterior := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [infty_not_mem_extendedUnitDisc, infty_mem_extendedUnitDiscExterior]
  | coe z =>
    simp only [mem_compl_iff, complexCircle_coe, sub_zero, mem_union,
      Hyperbolic.coe_mem_extendedUnitDisc, coe_mem_extendedUnitDiscExterior, ne_iff_lt_or_gt]

theorem reciprocal_mem_disc_iff_exterior (z : ExtendedComplex) :
    reciprocal z ∈ Hyperbolic.extendedUnitDisc ↔ z ∈ extendedUnitDiscExterior := by
  induction z using OnePoint.rec with
  | infty => simp [reciprocal_infty, infty_mem_extendedUnitDiscExterior, Hyperbolic.coe_mem_extendedUnitDisc]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [reciprocal_zero, infty_not_mem_extendedUnitDisc, coe_mem_extendedUnitDiscExterior]
    · rw [reciprocal_coe z hz, Hyperbolic.coe_mem_extendedUnitDisc, coe_mem_extendedUnitDiscExterior, norm_inv]
      exact inv_lt_one₀ (norm_pos_iff.mpr hz)

/-- Any two genuine generalized circles are carried to one another by an actual Möbius map. -/
theorem IsComplexGeneralizedCircle.exists_map {S T : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) (hT : IsComplexGeneralizedCircle T) :
    ∃ q : complexMobiusGroup, (q : Equiv.Perm ExtendedComplex) '' S = T := by
  obtain ⟨s, hs⟩ := hS.normalize_to_realAxis
  obtain ⟨t, ht⟩ := hT.normalize_to_realAxis
  refine ⟨t⁻¹ * s, ?_⟩
  have himage : ((t⁻¹ * s : complexMobiusGroup) : Equiv.Perm ExtendedComplex) '' S =
      (t⁻¹ : complexMobiusGroup).val '' ((s : Equiv.Perm ExtendedComplex) '' S) := by
    rw [Set.image_image]
    rfl
  rw [himage, hs, ← ht, Set.image_image]
  change ((fun z => (t : Equiv.Perm ExtendedComplex).symm ((t : Equiv.Perm ExtendedComplex) z)) '' T) = T
  simp

/-- Generalized-disc components are transported by the genuine boundary homeomorphism. -/
theorem IsComplexOpenDisc.image {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (f : complexMobiusGroup) : IsComplexOpenDisc ((f : Equiv.Perm ExtendedComplex) '' D) := by
  obtain ⟨S, hS, z, hz, rfl⟩ := hD
  refine ⟨(f : Equiv.Perm ExtendedComplex) '' S, hS.image f.property.1,
    (f : Equiv.Perm ExtendedComplex) z, ?_, ?_⟩
  · rw [← (f : Equiv.Perm ExtendedComplex).image_compl S]
    exact ⟨z, hz, rfl⟩
  · have hc := (mobiusBoundaryHomeomorph f).image_connectedComponentIn hz
    change (f : Equiv.Perm ExtendedComplex) '' connectedComponentIn Sᶜ z =
      connectedComponentIn ((f : Equiv.Perm ExtendedComplex) '' S)ᶜ ((f : Equiv.Perm ExtendedComplex) z)
    change (f : Equiv.Perm ExtendedComplex) '' connectedComponentIn Sᶜ z =
      connectedComponentIn ((f : Equiv.Perm ExtendedComplex) '' Sᶜ) ((f : Equiv.Perm ExtendedComplex) z) at hc
    rw [(f : Equiv.Perm ExtendedComplex).image_compl S] at hc
    exact hc

theorem connectedComponentIn_unitCircle_compl_of_mem_disc {z : ExtendedComplex}
    (hz : z ∈ Hyperbolic.extendedUnitDisc) :
    connectedComponentIn (complexCircle 0 1)ᶜ z = Hyperbolic.extendedUnitDisc := by
  have hsub : Hyperbolic.extendedUnitDisc ⊆ (complexCircle 0 1)ᶜ := by
    rw [unitCircle_compl_eq_disc_union_exterior]
    exact subset_union_left
  apply Subset.antisymm
  · apply IsPreconnected.subset_left_of_subset_union isOpen_extendedUnitDisc
      isOpen_extendedUnitDiscExterior disjoint_extendedUnitDisc_exterior
    · rw [← unitCircle_compl_eq_disc_union_exterior]
      exact connectedComponentIn_subset _ _
    · exact ⟨z, mem_connectedComponentIn (hsub hz), hz⟩
    · exact isPreconnected_connectedComponentIn
  · exact isConnected_extendedUnitDisc.isPreconnected.subset_connectedComponentIn hz hsub

theorem reciprocal_mem_exterior_iff_disc (z : ExtendedComplex) :
    reciprocal z ∈ extendedUnitDiscExterior ↔ z ∈ Hyperbolic.extendedUnitDisc := by
  have h := (reciprocal_mem_disc_iff_exterior (reciprocal z)).symm
  rw [reciprocal_involutive z] at h
  exact h

/-- Every genuine generalized circle admits a unit-circle normalization in the actual group. -/
theorem IsComplexGeneralizedCircle.normalize_to_unitCircle {S : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) :
    ∃ q : complexMobiusGroup, (q : Equiv.Perm ExtendedComplex) '' S = complexCircle 0 1 :=
  hS.exists_map (complexCircle_isGeneralized 0 1 zero_lt_one)

theorem reciprocal_image_exterior : reciprocal '' extendedUnitDiscExterior = Hyperbolic.extendedUnitDisc := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (reciprocal_mem_disc_iff_exterior w).mpr hw
  · intro hz
    exact ⟨reciprocal z, (reciprocal_mem_exterior_iff_disc z).mpr hz, reciprocal_involutive z⟩

theorem reciprocal_image_disc : reciprocal '' Hyperbolic.extendedUnitDisc = extendedUnitDiscExterior := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (reciprocal_mem_exterior_iff_disc w).mpr hw
  · intro hz
    exact ⟨reciprocal z, (reciprocal_mem_disc_iff_exterior z).mpr hz, reciprocal_involutive z⟩

theorem isConnected_extendedUnitDiscExterior : IsConnected extendedUnitDiscExterior := by
  rw [← reciprocal_image_disc]
  exact isConnected_extendedUnitDisc.image reciprocal continuous_reciprocal.continuousOn

theorem connectedComponentIn_unitCircle_compl_of_mem_exterior {z : ExtendedComplex}
    (hz : z ∈ extendedUnitDiscExterior) :
    connectedComponentIn (complexCircle 0 1)ᶜ z = extendedUnitDiscExterior := by
  have hsub : extendedUnitDiscExterior ⊆ (complexCircle 0 1)ᶜ := by
    rw [unitCircle_compl_eq_disc_union_exterior]
    exact subset_union_right
  apply Subset.antisymm
  · apply IsPreconnected.subset_right_of_subset_union isOpen_extendedUnitDisc
      isOpen_extendedUnitDiscExterior disjoint_extendedUnitDisc_exterior
    · rw [← unitCircle_compl_eq_disc_union_exterior]
      exact connectedComponentIn_subset _ _
    · exact ⟨z, mem_connectedComponentIn (hsub hz), hz⟩
    · exact isPreconnected_connectedComponentIn
  · exact isConnected_extendedUnitDiscExterior.isPreconnected.subset_connectedComponentIn hz hsub

/-- Every geometric generalized disc can be normalized to the actual open unit disc. -/
theorem IsComplexOpenDisc.normalize {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D) :
    ∃ q : complexMobiusGroup, (q : Equiv.Perm ExtendedComplex) '' D = Hyperbolic.extendedUnitDisc := by
  obtain ⟨S, hS, z, hz, rfl⟩ := hD
  obtain ⟨q, hq⟩ := hS.normalize_to_unitCircle
  have hc := (mobiusBoundaryHomeomorph q).image_connectedComponentIn hz
  change (q : Equiv.Perm ExtendedComplex) '' connectedComponentIn Sᶜ z =
    connectedComponentIn ((q : Equiv.Perm ExtendedComplex) '' Sᶜ) ((q : Equiv.Perm ExtendedComplex) z) at hc
  rw [(q : Equiv.Perm ExtendedComplex).image_compl S, hq] at hc
  have hzq : (q : Equiv.Perm ExtendedComplex) z ∈ (complexCircle 0 1)ᶜ := by
    rw [← hq, ← (q : Equiv.Perm ExtendedComplex).image_compl S]
    exact ⟨z, hz, rfl⟩
  rw [unitCircle_compl_eq_disc_union_exterior] at hzq
  rcases hzq with hi | ho
  · exact ⟨q, hc.trans (connectedComponentIn_unitCircle_compl_of_mem_disc hi)⟩
  · refine ⟨reciprocalMobius * q, ?_⟩
    change ((fun w => reciprocal ((q : Equiv.Perm ExtendedComplex) w)) ''
      connectedComponentIn Sᶜ z) = _
    rw [← Set.image_image, hc, connectedComponentIn_unitCircle_compl_of_mem_exterior ho,
      reciprocal_image_exterior]

/-- A complementary-disc component is genuinely open in the compactified complex topology. -/
theorem IsComplexOpenDisc.isOpen {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D) :
    IsOpen D := by
  obtain ⟨q, hq⟩ := hD.normalize
  apply (mobiusBoundaryHomeomorph q).isOpen_image.mp
  change IsOpen ((q : Equiv.Perm ExtendedComplex) '' D)
  rw [hq]
  exact isOpen_extendedUnitDisc

/-- A complementary-disc component is genuinely connected, rather than an arbitrary invariant set. -/
theorem IsComplexOpenDisc.isConnected {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D) :
    IsConnected D := by
  obtain ⟨q, hq⟩ := hD.normalize
  apply (mobiusBoundaryHomeomorph q).isConnected_image.mp
  change IsConnected ((q : Equiv.Perm ExtendedComplex) '' D)
  rw [hq]
  exact isConnected_extendedUnitDisc

end LowDimensionalTopology.Geometry.Mobius
