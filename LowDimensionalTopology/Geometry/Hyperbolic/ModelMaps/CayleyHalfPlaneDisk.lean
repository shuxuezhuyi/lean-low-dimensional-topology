/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.PoincareDensity
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.CurveLength
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.PoissonKernel
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Tactic

/-!
# Changes of hyperbolic model

Real positive-determinant matrices act on actual weighted curves. The determinant
is retained in the complex derivative and cancels against the imaginary-part
transformation; no determinant-one hypothesis is imposed.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc ENNReal Topology MatrixGroups ComplexConjugate

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- Positive-determinant real Möbius maps preserve the weighted norm of tangent vectors. -/
theorem gl_pos_weighted_tangent_norm (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (z : ℍ) (v : ℂ) :
    ‖((g.val.det : ℂ) / (UpperHalfPlane.denom g z) ^ 2) * v‖ / (g • z).im =
      ‖v‖ / z.im := by
  have hd := UpperHalfPlane.denom_ne_zero g z
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    UpperHalfPlane.im_smul_eq_div_normSq, Matrix.GeneralLinearGroup.val_det_apply,
    abs_of_pos hg, Complex.normSq_eq_norm_sq]
  field_simp

/-- Apply an arbitrary real positive-determinant Möbius map to a C¹ piece. -/
def C1CurvePiece.mapGLPos (c : C1CurvePiece) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    C1CurvePiece where
  a := c.a
  b := c.b
  ordered := c.ordered
  curve t := g • c.curve t
  velocity t := ((g.val.det : ℂ) / (UpperHalfPlane.denom g (c.curve t)) ^ 2) * c.velocity t
  continuous_curve := (continuous_const_smul g).comp_continuousOn c.continuous_curve
  continuous_velocity := by
    have hd : ContinuousOn (fun t => UpperHalfPlane.denom g (c.curve t)) (Icc c.a c.b) := by
      exact (continuousOn_const.mul
        (UpperHalfPlane.continuous_coe.comp_continuousOn c.continuous_curve)).add continuousOn_const
    exact (continuousOn_const.div (hd.pow 2)
      (fun t _ => pow_ne_zero 2 (UpperHalfPlane.denom_ne_zero _ _))).mul c.continuous_velocity
  hasDerivWithin t ht := by
    have hout := (UpperHalfPlane.hasStrictDerivAt_smul hg (c.curve t)).hasDerivAt
    have hcomp := hout.scomp_hasDerivWithinAt t (c.hasDerivWithin t ht)
    simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply, smul_eq_mul, mul_comm] using hcomp

/-- Weighted speeds are invariant, without requiring determinant one. -/
theorem C1CurvePiece.mapGLPos_speed (c : C1CurvePiece) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) (t : ℝ) :
    weightedSpeed (c.mapGLPos g hg).curve (c.mapGLPos g hg).velocity t =
      weightedSpeed c.curve c.velocity t :=
  gl_pos_weighted_tangent_norm g hg (c.curve t) (c.velocity t)

/-- The weighted length integral is invariant under every positive-determinant real Möbius map. -/
theorem C1CurvePiece.mapGLPos_length (c : C1CurvePiece) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) : (c.mapGLPos g hg).length = c.length := by
  apply intervalIntegral.integral_congr
  intro t _
  exact c.mapGLPos_speed g hg t

/-- Apply the transformation independently on every C¹ piece, retaining all joins. -/
def PiecewiseC1Curve.mapGLPos {z w : ℍ} (c : PiecewiseC1Curve z w)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) : PiecewiseC1Curve (g • z) (g • w) := by
  induction c with
  | nil z => exact .nil _
  | cons p tail ih => exact .cons (p.mapGLPos g hg) ih

theorem PiecewiseC1Curve.mapGLPos_length {z w : ℍ} (c : PiecewiseC1Curve z w)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) : (c.mapGLPos g hg).length = c.length := by
  induction c with
  | nil z => rfl
  | cons p tail ih =>
    change (p.mapGLPos g hg).length + (tail.mapGLPos g hg).length = p.length + tail.length
    rw [p.mapGLPos_length, ih]

/-- Mapping admissible curves gives one comparison of the genuine length infima. -/
theorem piecewisePathEDist_gl_pos_le (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z w : ℍ) :
    piecewisePathEDist (g • z) (g • w) ≤ piecewisePathEDist z w := by
  apply le_iInf
  intro c
  calc
    piecewisePathEDist (g • z) (g • w) ≤ ENNReal.ofReal (c.mapGLPos g hg).length :=
      iInf_le _ _
    _ = ENNReal.ofReal c.length := by rw [c.mapGLPos_length]

/-- Positive determinant is preserved by inversion. -/
theorem gl_pos_inverse (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    0 < (g⁻¹).val.det := by
  have h : 0 < (g.det : ℝ) := hg
  simpa only [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val] using
    inv_pos.mpr h

/-- For all real positive-determinant matrices. -/
theorem piecewisePathEDist_gl_pos (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z w : ℍ) :
    piecewisePathEDist (g • z) (g • w) = piecewisePathEDist z w := by
  apply le_antisymm (piecewisePathEDist_gl_pos_le g hg z w)
  have h := piecewisePathEDist_gl_pos_le g⁻¹ (gl_pos_inverse g hg) (g • z) (g • w)
  simpa only [inv_smul_smul] using h

/-- The same invariance for the real path distance of this formulation. -/
theorem path_distance_gl_pos (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z w : ℍ) :
    piecewisePathDist (g • z) (g • w) = piecewisePathDist z w := by
  unfold piecewisePathDist
  rw [piecewisePathEDist_gl_pos g hg]

/-- The existing upper-half-plane metric is invariant under every positive-determinant real matrix. -/
theorem metric_distance_gl_pos (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z w : ℍ) :
    dist (g • z) (g • w) = dist z w := by
  simpa only [piecewisePathDist_eq_metric] using path_distance_gl_pos g hg z w

/-- The Cayley map used. -/
def cayleyFormula (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

/-- The inverse Cayley formula on the unit disc. -/
def inverseCayleyFormula (z : ℂ) : ℂ := Complex.I * ((1 + z) / (1 - z))

theorem cayley_denom_ne_zero (z : ℍ) : (z : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im, UpperHalfPlane.coe_im] at hi
  linarith [z.im_pos]

theorem cayley_mem_disc (z : ℍ) : ‖cayleyFormula z‖ < 1 := by
  have hlt : ‖(z : ℂ) - Complex.I‖ < ‖(z : ℂ) + Complex.I‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
      UpperHalfPlane.coe_im]
    nlinarith [z.im_pos]
  rw [cayleyFormula, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (cayley_denom_ne_zero z))).mpr hlt

/-- The actual Cayley map from the upper half-plane to the unit disc. -/
def halfPlaneToDisc (z : ℍ) : 𝔻 := Complex.UnitDisc.mk (cayleyFormula z) (cayley_mem_disc z)

theorem inverseCayley_denom_ne_zero (z : 𝔻) : (1 : ℂ) - z ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm z.coe_ne_one)

theorem inverseCayley_im_pos (z : 𝔻) : 0 < (inverseCayleyFormula z).im := by
  have h := Auxiliary.Analysis.boundaryCayley_mapsTo (ζ := (1 : ℂ)) (by simp) z.norm_lt_one
  change 0 < (Auxiliary.Analysis.boundaryCayley 1 z).re at h
  simpa only [inverseCayleyFormula, Auxiliary.Analysis.boundaryCayley, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using h

/-- The inverse model map, with positivity proved from the unit-disc condition. -/
def discToHalfPlane (z : 𝔻) : ℍ := UpperHalfPlane.mk (inverseCayleyFormula z)
  (inverseCayley_im_pos z)

theorem discToHalfPlane_halfPlaneToDisc (z : ℍ) :
    discToHalfPlane (halfPlaneToDisc z) = z := by
  apply UpperHalfPlane.coe_injective
  change inverseCayleyFormula (cayleyFormula z) = (z : ℂ)
  have hd : 1 - cayleyFormula z ≠ 0 := inverseCayley_denom_ne_zero (halfPlaneToDisc z)
  unfold inverseCayleyFormula
  rw [← mul_div_assoc]
  apply (div_eq_iff hd).mpr
  unfold cayleyFormula
  field_simp [cayley_denom_ne_zero z]
  simp
  ring

theorem halfPlaneToDisc_discToHalfPlane (z : 𝔻) :
    halfPlaneToDisc (discToHalfPlane z) = z := by
  apply Complex.UnitDisc.coe_injective
  change cayleyFormula (inverseCayleyFormula z) = (z : ℂ)
  have hd : inverseCayleyFormula z + Complex.I ≠ 0 := cayley_denom_ne_zero (discToHalfPlane z)
  unfold cayleyFormula
  apply (div_eq_iff hd).mpr
  unfold inverseCayleyFormula
  field_simp [inverseCayley_denom_ne_zero z]
  simp
  ring

/-- The two model maps are a proved bijection. -/
def cayleyEquiv : ℍ ≃ 𝔻 where
  toFun := halfPlaneToDisc
  invFun := discToHalfPlane
  left_inv := discToHalfPlane_halfPlaneToDisc
  right_inv := halfPlaneToDisc_discToHalfPlane

/-- The differential of the specified half-plane-to-disc Cayley map. -/
theorem hasDerivAt_cayleyFormula (z : ℍ) :
    HasDerivAt cayleyFormula ((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) (z : ℂ) := by
  unfold cayleyFormula
  convert! ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).div
    ((hasDerivAt_id (z : ℂ)).add_const Complex.I) (cayley_denom_ne_zero z) using 1
  simp only [id_eq]
  ring

/-- The differential of the inverse Cayley formula on the actual unit disc. -/
theorem hasDerivAt_inverseCayleyFormula (z : 𝔻) :
    HasDerivAt inverseCayleyFormula ((2 * Complex.I) / (1 - (z : ℂ)) ^ 2) (z : ℂ) := by
  have hn : HasDerivAt (fun w : ℂ => 1 + w) 1 (z : ℂ) :=
    (hasDerivAt_id _).const_add 1
  have hd : HasDerivAt (fun w : ℂ => 1 - w) (-1) (z : ℂ) := by
    convert! (hasDerivAt_const (z : ℂ) (1 : ℂ)).sub (hasDerivAt_id _) using 1
    simp
  unfold inverseCayleyFormula
  convert! (hn.div hd (inverseCayley_denom_ne_zero z)).const_mul Complex.I using 1
  ring

/-- The real denominator identity relating the two hyperbolic densities. -/
theorem cayley_one_sub_norm_sq (z : ℍ) :
    1 - ‖cayleyFormula z‖ ^ 2 = 4 * z.im / ‖(z : ℂ) + Complex.I‖ ^ 2 := by
  have hn : ‖(z : ℂ) + Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_denom_ne_zero z)
  rw [cayleyFormula, norm_div, div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hn)).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hn)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    UpperHalfPlane.coe_im]
  ring

/-- The inverse imaginary part is the disc Poisson kernel. -/
theorem inverseCayley_im (z : 𝔻) :
    (inverseCayleyFormula z).im = (1 - ‖(z : ℂ)‖ ^ 2) / ‖1 - (z : ℂ)‖ ^ 2 := by
  have h := Auxiliary.Analysis.discPoissonKernel_eq_re_boundaryCayley (z : ℂ) (ζ := 1) (by simp)
  simp only [inverseCayleyFormula, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add]
  change (Auxiliary.Analysis.boundaryCayley 1 z).re = _
  rw [← h]
  simp only [Auxiliary.Analysis.discPoissonKernel, norm_sub_rev (z : ℂ) 1]

/-- The forward Cayley differential preserves the actual weighted tangent length. -/
theorem cayley_weighted_tangent_norm (z : ℍ) (v : ℂ) :
    2 * ‖((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) * v‖ /
        (1 - ‖cayleyFormula z‖ ^ 2) = ‖v‖ / z.im := by
  have hn : ‖(z : ℂ) + Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_denom_ne_zero z)
  rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, norm_pow, cayley_one_sub_norm_sq]
  field_simp
  ring

/-- The inverse differential preserves the disc density as well. -/
theorem inverseCayley_weighted_tangent_norm (z : 𝔻) (v : ℂ) :
    ‖((2 * Complex.I) / (1 - (z : ℂ)) ^ 2) * v‖ / (inverseCayleyFormula z).im =
      2 * ‖v‖ / (1 - ‖(z : ℂ)‖ ^ 2) := by
  have hn : ‖1 - (z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero z)
  rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, norm_pow, inverseCayley_im]
  field_simp

theorem continuous_halfPlaneToDisc : Continuous halfPlaneToDisc := by
  apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : ℍ => cayleyFormula z)
  exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
    (UpperHalfPlane.continuous_coe.add continuous_const) cayley_denom_ne_zero

theorem continuous_discToHalfPlane : Continuous discToHalfPlane := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : 𝔻 => inverseCayleyFormula z)
  exact continuous_const.mul ((continuous_const.add Complex.UnitDisc.continuous_coe).div
    (continuous_const.sub Complex.UnitDisc.continuous_coe) inverseCayley_denom_ne_zero)

/-- The Cayley bijection also respects the original Euclidean model topologies. -/
def cayleyHomeomorph : ℍ ≃ₜ 𝔻 where
  toEquiv := cayleyEquiv
  continuous_toFun := continuous_halfPlaneToDisc
  continuous_invFun := continuous_discToHalfPlane

/-- The disc density specified by. -/
def discWeightedSpeed (γ : ℝ → 𝔻) (v : ℝ → ℂ) (t : ℝ) : ℝ :=
  poincareLengthDensity (γ t : ℂ) * ‖v t‖

/-- The explicit speed formula is retained independently of the density implementation. -/
theorem discWeightedSpeed_formula (γ : ℝ → 𝔻) (v : ℝ → ℂ) (t : ℝ) :
    discWeightedSpeed γ v t = 2 * ‖v t‖ / (1 - ‖(γ t : ℂ)‖ ^ 2) :=
  poincareLengthDensity_mul_norm (γ t : ℂ) (v t)

/-- The curve speed uses the common Poincaré length factor. -/
theorem discWeightedSpeed_eq_poincareLengthDensity (γ : ℝ → 𝔻) (v : ℝ → ℂ) (t : ℝ) :
    discWeightedSpeed γ v t = poincareLengthDensity (γ t : ℂ) * ‖v t‖ := rfl

/-- A C¹ piece in the actual unit disc, with one-sided endpoint derivatives. -/
structure DiscC1CurvePiece where
  a : ℝ
  b : ℝ
  ordered : a ≤ b
  curve : ℝ → 𝔻
  velocity : ℝ → ℂ
  continuous_curve : ContinuousOn curve (Icc a b)
  continuous_velocity : ContinuousOn velocity (Icc a b)
  hasDerivWithin : ∀ t ∈ Icc a b,
    HasDerivWithinAt (fun s => (curve s : ℂ)) (velocity t) (Icc a b) t

def DiscC1CurvePiece.length (c : DiscC1CurvePiece) : ℝ :=
  ∫ t in c.a..c.b, discWeightedSpeed c.curve c.velocity t

/-- Cayley transports each admissible half-plane piece to an admissible disc piece. -/
def C1CurvePiece.toDisc (c : C1CurvePiece) : DiscC1CurvePiece where
  a := c.a
  b := c.b
  ordered := c.ordered
  curve t := halfPlaneToDisc (c.curve t)
  velocity t := ((2 * Complex.I) / ((c.curve t : ℂ) + Complex.I) ^ 2) * c.velocity t
  continuous_curve := continuous_halfPlaneToDisc.comp_continuousOn c.continuous_curve
  continuous_velocity := by
    have hd : ContinuousOn (fun t => (c.curve t : ℂ) + Complex.I) (Icc c.a c.b) :=
      (UpperHalfPlane.continuous_coe.comp_continuousOn c.continuous_curve).add continuousOn_const
    exact (continuousOn_const.div (hd.pow 2)
      (fun t _ => pow_ne_zero 2 (cayley_denom_ne_zero _))).mul c.continuous_velocity
  hasDerivWithin t ht := by
    have hcomp := (hasDerivAt_cayleyFormula (c.curve t)).scomp_hasDerivWithinAt t
      (c.hasDerivWithin t ht)
    change HasDerivWithinAt (fun s => cayleyFormula (c.curve s)) _ _ _
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hcomp

theorem C1CurvePiece.toDisc_speed (c : C1CurvePiece) (t : ℝ) :
    discWeightedSpeed c.toDisc.curve c.toDisc.velocity t =
      weightedSpeed c.curve c.velocity t := by
  rw [discWeightedSpeed_formula]
  exact cayley_weighted_tangent_norm (c.curve t) (c.velocity t)

theorem C1CurvePiece.toDisc_length (c : C1CurvePiece) : c.toDisc.length = c.length := by
  apply intervalIntegral.integral_congr
  intro t _
  exact c.toDisc_speed t

/-- The inverse map transports all disc C¹ pieces, including their endpoint derivatives. -/
def DiscC1CurvePiece.toHalfPlane (c : DiscC1CurvePiece) : C1CurvePiece where
  a := c.a
  b := c.b
  ordered := c.ordered
  curve t := discToHalfPlane (c.curve t)
  velocity t := ((2 * Complex.I) / (1 - (c.curve t : ℂ)) ^ 2) * c.velocity t
  continuous_curve := continuous_discToHalfPlane.comp_continuousOn c.continuous_curve
  continuous_velocity := by
    have hd : ContinuousOn (fun t => (1 : ℂ) - c.curve t) (Icc c.a c.b) :=
      continuousOn_const.sub (Complex.UnitDisc.continuous_coe.comp_continuousOn c.continuous_curve)
    exact (continuousOn_const.div (hd.pow 2)
      (fun t _ => pow_ne_zero 2 (inverseCayley_denom_ne_zero _))).mul c.continuous_velocity
  hasDerivWithin t ht := by
    have hcomp := (hasDerivAt_inverseCayleyFormula (c.curve t)).scomp_hasDerivWithinAt t
      (c.hasDerivWithin t ht)
    change HasDerivWithinAt (fun s => inverseCayleyFormula (c.curve s)) _ _ _
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hcomp

theorem DiscC1CurvePiece.toHalfPlane_speed (c : DiscC1CurvePiece) (t : ℝ) :
    weightedSpeed c.toHalfPlane.curve c.toHalfPlane.velocity t =
      discWeightedSpeed c.curve c.velocity t := by
  rw [discWeightedSpeed_formula]
  exact inverseCayley_weighted_tangent_norm (c.curve t) (c.velocity t)

theorem DiscC1CurvePiece.toHalfPlane_length (c : DiscC1CurvePiece) :
    c.toHalfPlane.length = c.length := by
  apply intervalIntegral.integral_congr
  intro t _
  exact c.toHalfPlane_speed t

/-- Finite piecewise C¹ curves in the unit disc. -/
inductive DiscPiecewiseC1Curve : 𝔻 → 𝔻 → Type where
  | nil (z : 𝔻) : DiscPiecewiseC1Curve z z
  | cons (c : DiscC1CurvePiece) {w : 𝔻}
      (tail : DiscPiecewiseC1Curve (c.curve c.b) w) : DiscPiecewiseC1Curve (c.curve c.a) w

def DiscPiecewiseC1Curve.length {z w : 𝔻} : DiscPiecewiseC1Curve z w → ℝ
  | .nil _ => 0
  | .cons c tail => c.length + tail.length

def PiecewiseC1Curve.toDisc {z w : ℍ} (c : PiecewiseC1Curve z w) :
    DiscPiecewiseC1Curve (halfPlaneToDisc z) (halfPlaneToDisc w) := by
  induction c with
  | nil z => exact .nil _
  | cons p tail ih => exact .cons p.toDisc ih

theorem PiecewiseC1Curve.toDisc_length {z w : ℍ} (c : PiecewiseC1Curve z w) :
    c.toDisc.length = c.length := by
  induction c with
  | nil z => rfl
  | cons p tail ih =>
    change p.toDisc.length + tail.toDisc.length = p.length + tail.length
    rw [p.toDisc_length, ih]

def DiscPiecewiseC1Curve.toHalfPlane {z w : 𝔻} (c : DiscPiecewiseC1Curve z w) :
    PiecewiseC1Curve (discToHalfPlane z) (discToHalfPlane w) := by
  induction c with
  | nil z => exact .nil _
  | cons p tail ih => exact .cons p.toHalfPlane ih

theorem DiscPiecewiseC1Curve.toHalfPlane_length {z w : 𝔻} (c : DiscPiecewiseC1Curve z w) :
    c.toHalfPlane.length = c.length := by
  induction c with
  | nil z => rfl
  | cons p tail ih =>
    change p.toHalfPlane.length + tail.toHalfPlane.length = p.length + tail.length
    rw [p.toHalfPlane_length, ih]

/-- The unit-disc path distance uses the actual density `2 / (1 - ‖z‖²)`. -/
def discPathEDist (z w : 𝔻) : ℝ≥0∞ :=
  ⨅ c : DiscPiecewiseC1Curve z w, ENNReal.ofReal c.length

theorem discPathEDist_cayley_le (z w : ℍ) :
    discPathEDist (halfPlaneToDisc z) (halfPlaneToDisc w) ≤ piecewisePathEDist z w := by
  apply le_iInf
  intro c
  calc
    discPathEDist (halfPlaneToDisc z) (halfPlaneToDisc w) ≤ ENNReal.ofReal c.toDisc.length :=
      iInf_le _ _
    _ = ENNReal.ofReal c.length := by rw [c.toDisc_length]

theorem halfPlanePathEDist_inverse_le (z w : 𝔻) :
    piecewisePathEDist (discToHalfPlane z) (discToHalfPlane w) ≤ discPathEDist z w := by
  apply le_iInf
  intro c
  calc
    piecewisePathEDist (discToHalfPlane z) (discToHalfPlane w) ≤
        ENNReal.ofReal c.toHalfPlane.length := iInf_le _ _
    _ = ENNReal.ofReal c.length := by rw [c.toHalfPlane_length]

/-- Both maps preserve all admissible piecewise lengths, hence the two path infima coincide. -/
theorem discPathEDist_eq_halfPlane (z w : 𝔻) :
    discPathEDist z w = piecewisePathEDist (discToHalfPlane z) (discToHalfPlane w) := by
  apply le_antisymm
  · have h := discPathEDist_cayley_le (discToHalfPlane z) (discToHalfPlane w)
    simpa only [halfPlaneToDisc_discToHalfPlane] using h
  · exact halfPlanePathEDist_inverse_le z w

def discPathDist (z w : 𝔻) : ℝ := (discPathEDist z w).toReal

theorem discPathDist_eq_halfPlane (z w : 𝔻) :
    discPathDist z w = dist (discToHalfPlane z) (discToHalfPlane w) := by
  rw [discPathDist, discPathEDist_eq_halfPlane, piecewisePathEDist_eq_metric,
    ENNReal.toReal_ofReal dist_nonneg]

/-- The hyperbolic metric on the disc retains its original Euclidean subspace topology. -/
@[instance_reducible] def discHyperbolicMetric : MetricSpace 𝔻 :=
  Topology.IsEmbedding.comapMetricSpace discToHalfPlane cayleyHomeomorph.symm.isEmbedding

theorem discHyperbolicMetric_distance (z w : 𝔻) :
    letI := discHyperbolicMetric
    dist z w = discPathDist z w := by
  change dist (discToHalfPlane z) (discToHalfPlane w) = discPathDist z w
  exact (discPathDist_eq_halfPlane z w).symm

/-- The Cayley transformation is an actual isometry for the proved weighted path metric. -/
theorem cayley_isometry :
    letI := discHyperbolicMetric
    Isometry halfPlaneToDisc := by
  let := discHyperbolicMetric
  apply Isometry.of_dist_eq
  intro z w
  change dist (discToHalfPlane (halfPlaneToDisc z))
    (discToHalfPlane (halfPlaneToDisc w)) = dist z w
  rw [discToHalfPlane_halfPlaneToDisc, discToHalfPlane_halfPlaneToDisc]

theorem inverseCayley_sub (z w : 𝔻) :
    inverseCayleyFormula z - inverseCayleyFormula w =
      (2 * Complex.I * ((z : ℂ) - w)) / ((1 - (z : ℂ)) * (1 - (w : ℂ))) := by
  unfold inverseCayleyFormula
  field_simp [inverseCayley_denom_ne_zero z, inverseCayley_denom_ne_zero w]
  ring

/-- A two-point formula for the actual disc weighted-path distance. -/
theorem disc_cosh_distance (z w : 𝔻) :
    Real.cosh (discPathDist z w) = 1 + 2 * ‖(z : ℂ) - w‖ ^ 2 /
      ((1 - ‖(z : ℂ)‖ ^ 2) * (1 - ‖(w : ℂ)‖ ^ 2)) := by
  have hzn : ‖1 - (z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero z)
  have hwn : ‖1 - (w : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero w)
  have hz : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  have hw : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := sub_pos.mpr w.sq_norm_lt_one
  rw [discPathDist_eq_halfPlane, halfPlane_cosh_dist_eq_norm_sq_formula]
  simp only [discToHalfPlane, UpperHalfPlane.coe_mk, UpperHalfPlane.mk_im]
  rw [inverseCayley_sub, inverseCayley_im, inverseCayley_im]
  simp only [norm_div, norm_mul, Complex.norm_I, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, mul_one]
  field_simp [hzn, hwn]


theorem disc_sinh_half_distance_sq (z w : 𝔻) :
    Real.sinh (discPathDist z w / 2) ^ 2 = ‖(z : ℂ) - w‖ ^ 2 /
      ((1 - ‖(z : ℂ)‖ ^ 2) * (1 - ‖(w : ℂ)‖ ^ 2)) := by
  have h := Real.cosh_two_mul (discPathDist z w / 2)
  rw [show 2 * (discPathDist z w / 2) = discPathDist z w by ring,
    disc_cosh_distance] at h
  rw [mul_div_assoc] at h
  have hf := Real.cosh_sq_sub_sinh_sq (discPathDist z w / 2)
  nlinarith

theorem disc_norm_identity (z w : 𝔻) :
    ‖1 - (z : ℂ) * conj (w : ℂ)‖ ^ 2 = ‖(z : ℂ) - w‖ ^ 2 +
      (1 - ‖(z : ℂ)‖ ^ 2) * (1 - ‖(w : ℂ)‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  ring

theorem disc_cosh_half_distance_sq (z w : 𝔻) :
    Real.cosh (discPathDist z w / 2) ^ 2 = ‖1 - (z : ℂ) * conj (w : ℂ)‖ ^ 2 /
      ((1 - ‖(z : ℂ)‖ ^ 2) * (1 - ‖(w : ℂ)‖ ^ 2)) := by
  rw [Real.cosh_sq', disc_sinh_half_distance_sq, disc_norm_identity]
  have hz : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  have hw : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := sub_pos.mpr w.sq_norm_lt_one
  field_simp
  ring

theorem disc_log_denominator_pos (z w : 𝔻) :
    0 < ‖1 - (z : ℂ) * conj (w : ℂ)‖ - ‖(z : ℂ) - w‖ := by
  have hz : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  have hw : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := sub_pos.mpr w.sq_norm_lt_one
  have h := disc_norm_identity z w
  nlinarith [mul_pos hz hw, norm_nonneg (1 - (z : ℂ) * conj (w : ℂ)),
    norm_nonneg ((z : ℂ) - w)]

theorem disc_tanh_half_distance (z w : 𝔻) :
    Real.tanh (discPathDist z w / 2) = ‖(z : ℂ) - w‖ /
      ‖1 - (z : ℂ) * conj (w : ℂ)‖ := by
  have hd : 0 ≤ discPathDist z w := by rw [discPathDist_eq_halfPlane]; exact dist_nonneg
  have hb : 0 < ‖1 - (z : ℂ) * conj (w : ℂ)‖ :=
    (norm_nonneg ((z : ℂ) - w)).trans_lt (sub_pos.mp (disc_log_denominator_pos z w))
  have hn : 0 ≤ Real.tanh (discPathDist z w / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le
  have hz : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  have hw : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := sub_pos.mpr w.sq_norm_lt_one
  apply (sq_eq_sq₀ hn (div_nonneg (norm_nonneg _) hb.le)).mp
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, disc_sinh_half_distance_sq,
    disc_cosh_half_distance_sq, div_pow]
  field_simp [hz.ne', hw.ne']

/-- For the density-defined disc path distance. -/
theorem disc_distance_log_formula (z w : 𝔻) :
    discPathDist z w = Real.log
      ((‖1 - (z : ℂ) * conj (w : ℂ)‖ + ‖(z : ℂ) - w‖) /
        (‖1 - (z : ℂ) * conj (w : ℂ)‖ - ‖(z : ℂ) - w‖)) := by
  let a := ‖(z : ℂ) - w‖
  let b := ‖1 - (z : ℂ) * conj (w : ℂ)‖
  have hb : 0 < b := (norm_nonneg _).trans_lt (sub_pos.mp (disc_log_denominator_pos z w))
  have hx : a / b ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have ha : 0 ≤ a := norm_nonneg _
      linarith [div_nonneg ha hb.le]
    · rw [show a / b = Real.tanh (discPathDist z w / 2) from
        (disc_tanh_half_distance z w).symm]
      exact (Real.tanh_lt_one _).le
  have h := Real.artanh_tanh (discPathDist z w / 2)
  rw [disc_tanh_half_distance, Real.artanh_eq_half_log hx] at h
  have hr : (1 + a / b) / (1 - a / b) = (b + a) / (b - a) := by
    field_simp
  change (1 / 2 : ℝ) * Real.log ((1 + a / b) / (1 - a / b)) = discPathDist z w / 2 at h
  rw [hr] at h
  change discPathDist z w = Real.log ((b + a) / (b - a))
  linarith

/-- The radial distance formula, valid for every point of the unit disc. -/
theorem disc_radial_distance (z : 𝔻) :
    discPathDist 0 z = Real.log ((1 + ‖(z : ℂ)‖) / (1 - ‖(z : ℂ)‖)) := by
  simpa only [Complex.UnitDisc.coe_zero, zero_mul, sub_zero, norm_one, zero_sub, norm_neg] using
    disc_distance_log_formula 0 z

end

end LowDimensionalTopology.Geometry.Hyperbolic
