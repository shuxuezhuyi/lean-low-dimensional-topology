/- Actual infinity-centered clause, 2026-10-20. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedCircleSides
public import LowDimensionalTopology.Geometry.Mobius.Ford.ComplexFordRegions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology OnePoint Pointwise ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine complete finite-circle reflection exchanges its center and infinity. -/
theorem circleReflectionAction_circle_center (c : ℂ) (r : ℝ) (hr : 0 < r) :
    _root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r, _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_isGeneralized c r hr⟩ c = ∞ := by
  have he := _root_.LowDimensionalTopology.Geometry.Mobius.geometricCircleReflection_unique
    ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r,
      _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_isGeneralized c r hr⟩
    (_root_.LowDimensionalTopology.Geometry.Inversive.sphereInversionHomeomorph
      (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates c) r hr.ne')
    (_root_.LowDimensionalTopology.Geometry.Inversive.sphereInversion_isReflection _ _
      hr) (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_reflection c r hr)
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction, ← he]
  change _root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexEuclideanHomeomorph.symm
    (_root_.LowDimensionalTopology.Geometry.Inversive.sphereInversionHomeomorph
      (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates c) r hr.ne'
      (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates c :
        _root_.LowDimensionalTopology.Geometry.Inversive.ExtendedEuclidean 2)) = ∞
  simp [_root_.LowDimensionalTopology.Geometry.Inversive.sphereInversionHomeomorph_apply,
    _root_.LowDimensionalTopology.Geometry.Inversive.sphereInversion_center]

/-- A true line reflection fixes infinity and is a genuine finite Euclidean isometry. -/
theorem circleReflectionAction_line_isometry (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    ∃ f : ℂ ≃ᵢ ℂ, _root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction
      ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexLine a t,
        _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_isGeneralized a t ha⟩ =
        f.toHomeomorph.onePointCongr.toEquiv := by
  let e := _root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates
  let f : ℂ ≃ᵢ ℂ := (e.toIsometryEquiv.trans
    (_root_.LowDimensionalTopology.Geometry.Inversive.planeReflectionFiniteIsometry (e a) t)).trans
    e.symm.toIsometryEquiv
  refine ⟨f, ?_⟩
  have he := _root_.LowDimensionalTopology.Geometry.Mobius.geometricCircleReflection_unique
    ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexLine a t,
      _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_isGeneralized a t ha⟩
    (_root_.LowDimensionalTopology.Geometry.Inversive.planeReflectionHomeomorph (e a) t ((e.map_ne_zero_iff).mpr ha))
    (_root_.LowDimensionalTopology.Geometry.Inversive.planeReflection_isReflection _ _
      _) (_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_reflection a t ha)
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction, ← he]
  ext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change (e.symm (_root_.LowDimensionalTopology.Geometry.Inversive.planeReflectionFinite (e a) t (e z)) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (f z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    simp only [f, IsometryEquiv.trans_apply, LinearIsometryEquiv.coe_toIsometryEquiv,
      _root_.LowDimensionalTopology.Geometry.Inversive.planeReflectionFiniteIsometry_apply]

/-- In every actual model, the first infinity-normalized mirror is the original
complex isometric circle. The model boundary imposes no extra restriction. -/
theorem _root_.LowDimensionalTopology.Geometry.Mobius.IsGeometricNormalizedReflectionFactor.infty_first_isometricCircle
    {B S T : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle} (A :
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hc : A 1 0 ≠ 0)
    (h : _root_.LowDimensionalTopology.Geometry.Mobius.IsGeometricNormalizedReflectionFactor B
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A) ∞ S T) :
    S.val = _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (-A 1 1 / A 1 0)
      (_root_.LowDimensionalTopology.Geometry.Mobius.isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1)) := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have hdet0 : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hcoeff : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A).val =
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinearOfCoefficients (A 0 0) (A 0 1) (A 1 0) (A 1 1) hdet0 := by
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.specialLinear_projection_coe]
    apply congrArg _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hmoved : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A).val ∞ ≠ ∞ := by
    rw [hcoeff, _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinearOfCoefficients_infty, ite_eq_right hc]
    exact OnePoint.coe_ne_infty _
  have hSnot := h.first_mirror_avoids_center hmoved
  obtain (⟨c, r, hr, hS⟩ | ⟨a, t, ha, hS⟩) :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.isComplexGeneralizedCircle_iff S.val).mp S.property
  · have hSb : S = ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r,
    _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_isGeneralized c r hr⟩ := Subtype.ext hS
    subst S
    obtain (⟨c', r', hr', hT⟩ | ⟨a, t, ha, hT⟩) :=
      (_root_.LowDimensionalTopology.Geometry.Mobius.isComplexGeneralizedCircle_iff T.val).mp T.property
    · exact False.elim (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty c' r' (hT ▸ h.2.2.2))
    · have hTb : T = ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexLine a t,
      _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_isGeneralized a t ha⟩ := Subtype.ext hT
      subst T
      obtain ⟨f, hf⟩ := circleReflectionAction_line_isometry a t ha
      have hfac := h.2.2.1
      rw [hf] at hfac
      have hpole : _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinearOfCoefficients (A 0 0) (A 0 1) (A 1 0) (A 1 1) hdet0 c = ∞ := by
        rw [← hcoeff, hfac, Equiv.Perm.mul_apply, circleReflectionAction_circle_center c r hr]
        rfl
      have hc0 : c = -A 1 1 / A 1 0 :=
        (_root_.LowDimensionalTopology.Geometry.Mobius.denominator_eq_zero_iff _ _ _ hc).mp
          ((_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinearOfCoefficients_eq_infty_iff _ _ _ _ _
            hdet0).mp hpole)
      subst c
      let p : ℂ := -A 1 1 / A 1 0 + r
      let q : ℂ := -A 1 1 / A 1 0 - r
      have hp : (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (-A 1 1 / A 1 0) r := by
        simp [p, _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe, abs_of_pos hr]
      have hq : (q : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (-A 1 1 / A 1 0) r := by
        have he : q - (-A 1 1 / A 1 0) = -(r : ℂ) := by dsimp [q]; ring
        rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe, he, norm_neg, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr]
      have hdenp : A 1 0 * p + A 1 1 = A 1 0 * r := by dsimp [p]; field_simp; ring
      have hdenq : A 1 0 * q + A 1 1 = -(A 1 0 * r) := by dsimp [q]; field_simp; ring
      have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hdp : A 1 0 * p + A 1 1 ≠ 0 := by rw [hdenp]; exact mul_ne_zero hc hrC
      have hdq : A 1 0 * q + A 1 1 ≠ 0 := by rw [hdenq]; exact neg_ne_zero.mpr (mul_ne_zero hc hrC)
      have hfinite (z : ℂ) (hz : (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈
        _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (-A 1 1 / A 1 0) r)
          (hdz : A 1 0 * z + A 1 1 ≠ 0) :
          _root_.LowDimensionalTopology.Geometry.Mobius.fractionalValue (A 0 0) (A 0 1) (A 1 0) (A 1 1) z = f z := by
        have hfix : _root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction
            ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (-A 1 1 / A 1 0) r,
              _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_isGeneralized _ _ hr⟩ z = z :=
          show (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ Function.fixedPoints _ from
            (_root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction_fixedPoints _).symm ▸ hz
        have he := congrArg (fun u : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex => u
          z) hfac
        rw [hcoeff, _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinearOfCoefficients_finite _ _ _ _ _ _ hdz,
          Equiv.Perm.mul_apply, hfix] at he
        exact OnePoint.coe_injective he
      have hdist := _root_.LowDimensionalTopology.Geometry.Mobius.fractionalValue_dist (A 0 0) (A 0 1) (A 1 0) (A 1
        1) p q hdp hdq
      rw [hfinite p hp hdp, hfinite q hq hdq, f.dist_eq, hdet, norm_one, one_mul,
        hdenp, hdenq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr] at hdist
      have hpq : p ≠ q := by
        intro he
        have hh : (r : ℂ) = 0 := by dsimp [p, q] at he; linear_combination he / 2
        exact hrC hh
      have hdistpos : 0 < dist p q := dist_pos.mpr hpq
      have hcn : 0 < ‖A 1 0‖ := norm_pos_iff.mpr hc
      have hmul : ‖A 1 0‖ * r = 1 := by
        have hh := (eq_div_iff (mul_ne_zero (mul_pos hcn hr).ne' (mul_pos hcn hr).ne')).mp hdist
        have hs : (‖A 1 0‖ * r) ^ 2 = 1 := by nlinarith only [hh, hdistpos]
        nlinarith only [hs, mul_pos hcn hr]
      have hradius : r = _root_.LowDimensionalTopology.Geometry.Mobius.isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1) := by
        rw [_root_.LowDimensionalTopology.Geometry.Mobius.isometricCircleRadius, hdet, norm_one, Real.sqrt_one]
        exact (eq_div_iff hcn.ne').mpr (by simpa only [mul_comm] using hmul)
      change _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (-A 1 1 / A 1 0) r = _
      rw [hradius]
  · exact False.elim (hSnot (hS.symm ▸ _root_.LowDimensionalTopology.Geometry.Mobius.complexLine_infty a t))

/-- The literal infinity-centered generalized polygon equals the literal Ford
intersection in every original Fuchsian disc, including exterior models. -/
theorem generalizedDirichletPolygon_infty_eq_Ford_intersection
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hfree : ∀ g : H, g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ∞ → g = 1) :
    generalizedDirichletPolygon D ∞ hfree = D.carrier ∩ _root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexFordRegion H := by
  have hmirror (g : H) (hg : g ≠ 1) (A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2)
      (hA : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A = g.val) (hc : A 1 0 ≠ 0) :
      (_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors D.carrier D.isDisc g.val (D.image_eq g)
        ∞
        (freeMobiusCenter_moved ∞ hfree g hg)).1.val = _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (-A 1
          1 / A 1 0)
          (_root_.LowDimensionalTopology.Geometry.Mobius.isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1)) := by
    have hspec := _root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_spec D.carrier D.isDisc g.val (D.image_eq g) ∞
      (freeMobiusCenter_moved ∞ hfree g hg)
    apply _root_.LowDimensionalTopology.Geometry.Mobius.IsGeometricNormalizedReflectionFactor.infty_first_isometricCircle A hc
    exact ⟨hspec.1, hspec.2.1, hA.symm ▸ hspec.2.2.1, hspec.2.2.2⟩
  ext z
  rw [generalizedDirichletPolygon_mem_iff]
  constructor
  · rintro ⟨hz, hall⟩
    refine ⟨hz, ?_⟩
    intro A hA hc
    let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A, hA⟩
    have hg : g ≠ 1 := by
      intro he
      apply hc
      apply (_root_.LowDimensionalTopology.Geometry.Mobius.Classification.specialLinear_fixes_infty_iff A).mp
      change g.val.val ∞ = ∞
      rw [he]
      rfl
    have hi := hall g hg
    change z ∈ connectedComponentIn _ ∞ at hi
    rwa [hmirror g hg A rfl hc] at hi
  · rintro ⟨hz, hall⟩
    refine ⟨hz, ?_⟩
    intro g hg
    obtain ⟨A, hA, hc⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.free_infty_nonidentity_has_isometricCircle H hfree g hg
    change z ∈ connectedComponentIn _ ∞
    rw [hmirror g hg A hA hc]
    exact hall A (hA.symm ▸ g.property) hc

end LowDimensionalTopology.Geometry.Fuchsian
