/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenGapLocalFiniteness

/-!
# Actual finite Nielsen-core polygon geometry
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem nielsen_bounded_gap_line_re (a b : ℝ) (hab : a<b) (z : ℍ)
    (hz : z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).line.carrier) :
    a<z.re ∧ z.re<b := by
  have he := norm_sub_real_eq_radius_sq hz
  have hp := sq_pos_of_pos z.im_pos
  constructor <;> nlinarith [sq_nonneg (z.re-(a+b)/2)]

/-- Distinct actual disjoint ordinary real intervals have complete gap
geodesics which either coincide or have disjoint native carriers. -/
theorem nielsen_gap_lines_eq_or_disjoint (G J : NielsenHalfPlaneGap)
    (hd : Disjoint G.carrier J.carrier) :
    G.line=J.line ∨ Disjoint G.line.carrier J.line.carrier := by
  have hdb := disjoint_left.mp hd
  have hdb' := disjoint_left.mp hd.symm
  cases G with
  | bounded a b hab =>
    right
    apply disjoint_left.mpr
    intro z hzG hzJ
    have hx := nielsen_bounded_gap_line_re a b hab z hzG
    cases J with
    | bounded c d hcd =>
      exact hdb hx (nielsen_bounded_gap_line_re c d hcd z hzJ)
    | left c =>
      change z.re=c at hzJ
      apply hdb (a:=(a+c)/2)
      · change a<(a+c)/2 ∧ (a+c)/2<b
        constructor <;> linarith
      · change (a+c)/2<c
        linarith
    | right c =>
      change z.re=c at hzJ
      apply hdb (a:=(c+b)/2)
      · change a<(c+b)/2 ∧ (c+b)/2<b
        constructor <;> linarith
      · change c<(c+b)/2
        linarith
  | left b =>
    cases J with
    | bounded c d hcd =>
      right
      apply disjoint_left.mpr
      intro z hzG hzJ
      have hx := nielsen_bounded_gap_line_re c d hcd z hzJ
      change z.re=b at hzG
      apply hdb' (a:=(c+b)/2)
      · change c<(c+b)/2 ∧ (c+b)/2<d
        constructor <;> linarith
      · change (c+b)/2<b
        linarith
    | left c =>
      by_cases hbc : b=c
      · subst c; exact Or.inl rfl
      · right
        apply disjoint_left.mpr
        intro z hzG hzJ
        exact hbc (hzG.symm.trans hzJ)
    | right c =>
      by_cases hbc : b=c
      · subst c; exact Or.inl rfl
      · right
        apply disjoint_left.mpr
        intro z hzG hzJ
        exact hbc (hzG.symm.trans hzJ)
  | right a =>
    cases J with
    | bounded c d hcd =>
      right
      apply disjoint_left.mpr
      intro z hzG hzJ
      have hx := nielsen_bounded_gap_line_re c d hcd z hzJ
      change z.re=a at hzG
      apply hdb' (a:=(a+d)/2)
      · change c<(a+d)/2 ∧ (a+d)/2<d
        constructor <;> linarith
      · change a<(a+d)/2
        linarith
    | left b =>
      by_cases hab : a=b
      · subst b; exact Or.inl rfl
      · right
        apply disjoint_left.mpr
        intro z hzG hzJ
        exact hab (hzG.symm.trans hzJ)
    | right b =>
      by_cases hab : a=b
      · subst b; exact Or.inl rfl
      · right
        apply disjoint_left.mpr
        intro z hzG hzJ
        exact hab (hzG.symm.trans hzJ)

end LowDimensionalTopology.Geometry.Hyperbolic
