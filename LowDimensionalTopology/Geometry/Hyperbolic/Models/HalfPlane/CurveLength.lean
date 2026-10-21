/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.MetricFormulas
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.MobiusNormalization
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic

/-!
# Weighted lengths of piecewise C¹ curves

Pieces retain continuous velocities and derivatives within their closed parameter
intervals. Finite concatenations therefore allow the finitely many derivative
breaks admitted in this formulation. No equality between a path infimum and the existing
metric is included as an assumption.
-/

public section

open Set Filter MeasureTheory
open scoped UpperHalfPlane Topology MatrixGroups ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- The speed prescribed by differential. -/
@[expose] def weightedSpeed (γ : ℝ → ℍ) (v : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖v t‖ / (γ t).im

theorem weightedSpeed_nonneg (γ : ℝ → ℍ) (v : ℝ → ℂ) (t : ℝ) :
    0 ≤ weightedSpeed γ v t := by
  exact div_nonneg (norm_nonneg _) (γ t).im_pos.le

/-- One continuously differentiable piece, including its one-sided endpoint derivatives. -/
structure C1CurvePiece where
  a : ℝ
  b : ℝ
  ordered : a ≤ b
  curve : ℝ → ℍ
  velocity : ℝ → ℂ
  continuous_curve : ContinuousOn curve (Icc a b)
  continuous_velocity : ContinuousOn velocity (Icc a b)
  hasDerivWithin : ∀ t ∈ Icc a b,
    HasDerivWithinAt (fun s => (curve s : ℂ)) (velocity t) (Icc a b) t

/-- The integral of the weighted speed on a single C¹ piece. -/
@[expose] noncomputable def C1CurvePiece.length (c : C1CurvePiece) : ℝ :=
  ∫ t in c.a..c.b, weightedSpeed c.curve c.velocity t

/-- Within a closed interval, points before its right endpoint have the same right derivative. -/
theorem hasDerivWithinAt_right_of_Icc {f : ℝ → ℂ} {v : ℂ} {a b t : ℝ}
    (h : HasDerivWithinAt f v (Icc a b) t) (ht : t ∈ Ico a b) :
    HasDerivWithinAt f v (Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsb
  exact ⟨ht.1.trans hs, hsb.le⟩

/-- A differentiable curve gives the expected upper bound on the right distance slopes. -/
theorem distance_right_slope_bound {γ : ℝ → ℍ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivWithinAt (fun s => (γ s : ℂ)) v (Ici t) t)
    (p : ℍ) {r : ℝ} (hr : ‖v‖ / (γ t).im < r) :
    ∃ᶠ s in 𝓝[>] t, slope (fun s => dist p (γ s)) t s < r := by
  have hright := hγ.Ioi_of_Ici
  have hslope : Tendsto (slope (fun s => (γ s : ℂ)) t) (𝓝[>] t) (𝓝 v) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp hright
  have him : Tendsto (fun s => (γ s).im) (𝓝[>] t) (𝓝 (γ t).im) := by
    exact Complex.continuous_im.continuousAt.tendsto.comp hright.continuousWithinAt
  have hroot : Tendsto (fun s => Real.sqrt ((γ s).im * (γ t).im))
      (𝓝[>] t) (𝓝 (γ t).im) := by
    simpa only [Function.comp_def, Real.sqrt_mul_self (γ t).im_pos.le] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp (him.mul_const (γ t).im))
  have hquot := hslope.norm.div hroot (γ t).im_ne_zero
  have hevent : ∀ᶠ s in 𝓝[>] t,
      ‖slope (fun s => (γ s : ℂ)) t s‖ /
        Real.sqrt ((γ s).im * (γ t).im) < r :=
    hquot (Iio_mem_nhds hr)
  apply Filter.Eventually.frequently
  filter_upwards [hevent, self_mem_nhdsWithin] with s hs hst
  have hpos : 0 < s - t := sub_pos.mpr hst
  have htriangle : dist p (γ s) - dist p (γ t) ≤ dist (γ s) (γ t) := by
    have h := dist_triangle p (γ t) (γ s)
    rw [dist_comm (γ t) (γ s)] at h
    linarith
  calc
    slope (fun s => dist p (γ s)) t s
        ≤ dist (γ s) (γ t) / (s - t) := by
          rw [slope_def_field]
          exact div_le_div_of_nonneg_right htriangle hpos.le
    _ ≤ (dist (γ s : ℂ) (γ t) / Real.sqrt ((γ s).im * (γ t).im)) / (s - t) :=
      div_le_div_of_nonneg_right (UpperHalfPlane.dist_le_dist_coe_div_sqrt _ _) hpos.le
    _ = ‖slope (fun s => (γ s : ℂ)) t s‖ /
        Real.sqrt ((γ s).im * (γ t).im) := by
          simp only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_pos hpos, Complex.dist_eq]
          ring
    _ < r := hs

/-- The weighted speed of a C¹ piece is continuous on its parameter interval. -/
theorem C1CurvePiece.continuous_speed (c : C1CurvePiece) :
    ContinuousOn (weightedSpeed c.curve c.velocity) (Icc c.a c.b) :=
  c.continuous_velocity.norm.div
    (UpperHalfPlane.continuous_im.comp_continuousOn c.continuous_curve)
    (fun t _ => (c.curve t).im_ne_zero)

/-- Every C¹ piece has weighted length at least its actual hyperbolic displacement. -/
theorem C1CurvePiece.dist_le_length (c : C1CurvePiece) :
    dist (c.curve c.a) (c.curve c.b) ≤ c.length := by
  let β : ℝ → ℝ := IccExtend c.ordered
    (fun t : Icc c.a c.b => weightedSpeed c.curve c.velocity t)
  have hβ : Continuous β := c.continuous_speed.domRestrict.Icc_extend'
  have hβeq (t : ℝ) (ht : t ∈ Icc c.a c.b) :
      β t = weightedSpeed c.curve c.velocity t :=
    IccExtend_of_mem c.ordered _ ht
  have hF : ContinuousOn (fun t => dist (c.curve c.a) (c.curve t)) (Icc c.a c.b) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk c.continuous_curve)
  have hB : Continuous (fun t => ∫ s in c.a..t, β s) :=
    intervalIntegral.continuous_primitive (fun a b => hβ.intervalIntegrable a b) c.a
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary hF
    (B := fun t => ∫ s in c.a..t, β s) (B' := β) (by simp) hB.continuousOn
    (fun t _ => (hβ.integral_hasStrictDerivAt c.a t).hasDerivAt.hasDerivWithinAt)
    (fun t ht r hr => distance_right_slope_bound
      (hasDerivWithinAt_right_of_Icc (c.hasDerivWithin t ⟨ht.1, ht.2.le⟩) ht)
      (c.curve c.a) (by simpa only [hβeq t ⟨ht.1, ht.2.le⟩, weightedSpeed] using hr))
  have hend := hbound (right_mem_Icc.mpr c.ordered)
  apply hend.trans_eq
  apply intervalIntegral.integral_congr
  intro t ht
  exact hβeq t (by simpa only [uIcc_of_le c.ordered] using ht)

/-- Finite concatenations allow derivative breaks at the joins. -/
inductive PiecewiseC1Curve : ℍ → ℍ → Type where
  | nil (z : ℍ) : PiecewiseC1Curve z z
  | cons (c : C1CurvePiece) {w : ℍ} (tail : PiecewiseC1Curve (c.curve c.b) w) :
      PiecewiseC1Curve (c.curve c.a) w

/-- The length of a finite piecewise C¹ curve is the sum of its piece lengths. -/
@[expose] def PiecewiseC1Curve.length {z w : ℍ} : PiecewiseC1Curve z w → ℝ
  | .nil _ => 0
  | .cons c tail => c.length + tail.length

/-- The lower bound applies to every finite number of C¹ pieces. -/
theorem PiecewiseC1Curve.dist_le_length {z w : ℍ} (c : PiecewiseC1Curve z w) :
    dist z w ≤ c.length := by
  induction c with
  | nil z => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length]
  | cons c tail ih =>
    exact (dist_triangle _ _ _).trans (add_le_add c.dist_le_length ih)

theorem PiecewiseC1Curve.length_nonneg {z w : ℍ} (c : PiecewiseC1Curve z w) :
    0 ≤ c.length := dist_nonneg.trans c.dist_le_length

/-- Concatenation does not require matching derivatives at the common endpoint. -/
@[expose] def PiecewiseC1Curve.append {x y z : ℍ} (c : PiecewiseC1Curve x y)
    (d : PiecewiseC1Curve y z) : PiecewiseC1Curve x z := by
  induction c with
  | nil _ => exact d
  | cons p tail ih => exact .cons p (ih d)

theorem PiecewiseC1Curve.append_length {x y z : ℍ} (c : PiecewiseC1Curve x y)
    (d : PiecewiseC1Curve y z) : (c.append d).length = c.length + d.length := by
  induction c with
  | nil _ => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.append,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length]
  | cons p tail ih =>
    change p.length + (tail.append d).length = (p.length + tail.length) + d.length
    rw [ih d, add_assoc]

/-- A single parametrized curve, with a finite partition and a continuous velocity on each piece. -/
structure PartitionedC1Curve where
  n : ℕ
  times : ℕ → ℝ
  curve : ℝ → ℍ
  velocity : ℕ → ℝ → ℂ
  ordered : ∀ i < n, times i ≤ times (i + 1)
  continuous_curve : ∀ i < n, ContinuousOn curve (Icc (times i) (times (i + 1)))
  continuous_velocity : ∀ i < n,
    ContinuousOn (velocity i) (Icc (times i) (times (i + 1)))
  hasDerivWithin : ∀ i < n, ∀ t ∈ Icc (times i) (times (i + 1)),
    HasDerivWithinAt (fun s => (curve s : ℂ)) (velocity i t)
      (Icc (times i) (times (i + 1))) t

/-- Restrict the partitioned curve to one closed interval. -/
@[expose] def PartitionedC1Curve.piece (c : PartitionedC1Curve) (i : ℕ) (hi : i < c.n) :
    C1CurvePiece where
  a := c.times i
  b := c.times (i + 1)
  ordered := c.ordered i hi
  curve := c.curve
  velocity := c.velocity i
  continuous_curve := c.continuous_curve i hi
  continuous_velocity := c.continuous_velocity i hi
  hasDerivWithin := c.hasDerivWithin i hi

/-- The first `k` partition intervals give a finite piecewise curve with the stated endpoints. -/
@[expose] def PartitionedC1Curve.prefix (c : PartitionedC1Curve) :
    (k : ℕ) → k ≤ c.n → PiecewiseC1Curve (c.curve (c.times 0)) (c.curve (c.times k))
  | 0, _ => .nil _
  | k + 1, hk =>
      (c.prefix k (Nat.le_trans (Nat.le_succ k) hk)).append
        (.cons (c.piece k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) (.nil _))

/-- The usual partition integral is exactly the sum represented by finite concatenation. -/
theorem PartitionedC1Curve.prefix_length (c : PartitionedC1Curve) (k : ℕ) (hk : k ≤ c.n) :
    (c.prefix k hk).length =
      ∑ i ∈ Finset.range k, ∫ t in c.times i..c.times (i + 1),
        weightedSpeed c.curve (c.velocity i) t := by
  induction k with
  | zero => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PartitionedC1Curve.prefix,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length]
  | succ k ih =>
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PartitionedC1Curve.prefix]
    erw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.append_length]
    rw [ih (Nat.le_trans (Nat.le_succ k) hk), Finset.sum_range_succ]
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length, C1CurvePiece.length,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.PartitionedC1Curve.piece, add_zero]

/-- Every curve with a finite C¹ partition satisfies the integral lower bound. -/
theorem PartitionedC1Curve.dist_le_length (c : PartitionedC1Curve) :
    dist (c.curve (c.times 0)) (c.curve (c.times c.n)) ≤
      ∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
        weightedSpeed c.curve (c.velocity i) t := by
  rw [← c.prefix_length c.n le_rfl]
  exact (c.prefix c.n le_rfl).dist_le_length

/-- The extended infimum is defined using actual finite piecewise curves and weighted integrals. -/
@[expose] def piecewisePathEDist (z w : ℍ) : ℝ≥0∞ :=
  ⨅ c : PiecewiseC1Curve z w, ENNReal.ofReal c.length

/-- The integral lower bound passes to the infimum over all piecewise C¹ curves. -/
theorem metric_le_piecewisePathEDist (z w : ℍ) :
    ENNReal.ofReal (dist z w) ≤ piecewisePathEDist z w := by
  exact le_iInf fun c => ENNReal.ofReal_le_ofReal c.dist_le_length

/-- Apply a real determinant-one Möbius transformation to a C¹ piece. -/
@[expose] def C1CurvePiece.mapSL2 (c : C1CurvePiece) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    C1CurvePiece where
  a := c.a
  b := c.b
  ordered := c.ordered
  curve t := g • c.curve t
  velocity t := ((1 : ℂ) /
    (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (c.curve t)) ^ 2) * c.velocity t
  continuous_curve := (continuous_const_smul g).comp_continuousOn c.continuous_curve
  continuous_velocity := by
    have hd : ContinuousOn
        (fun t => UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (c.curve t))
        (Icc c.a c.b) := by
      exact (continuousOn_const.mul
        (UpperHalfPlane.continuous_coe.comp_continuousOn c.continuous_curve)).add continuousOn_const
    exact (continuousOn_const.div (hd.pow 2)
      (fun t _ => pow_ne_zero 2 (UpperHalfPlane.denom_ne_zero _ _))).mul c.continuous_velocity
  hasDerivWithin t ht := by
    have hpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ g).val.det := by simp
    have hout := (UpperHalfPlane.hasStrictDerivAt_smul hpos (c.curve t)).hasDerivAt
    have hcomp := hout.scomp_hasDerivWithinAt t (c.hasDerivWithin t ht)
    simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply,
      ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one, Complex.ofReal_one, smul_eq_mul, mul_comm,
      MulAction.compHom_smul_def] using hcomp

/-- Möbius transformations preserve the prescribed weighted speed pointwise. -/
theorem C1CurvePiece.mapSL2_speed (c : C1CurvePiece) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (t : ℝ) :
    weightedSpeed (c.mapSL2 g).curve (c.mapSL2 g).velocity t =
      weightedSpeed c.curve c.velocity t :=
  sl2_weighted_tangent_norm g (c.curve t) (c.velocity t)

/-- Möbius transformations preserve the weighted length integral of every C¹ piece. -/
theorem C1CurvePiece.mapSL2_length (c : C1CurvePiece) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (c.mapSL2 g).length = c.length := by
  apply intervalIntegral.integral_congr
  intro t _
  exact c.mapSL2_speed g t

/-- A vertical curve with exponential height, so that its weighted speed is constant. -/
@[expose] def verticalPiece (x p q : ℝ) (_hp : 0 < p) (_hq : 0 < q) : C1CurvePiece where
  a := 0
  b := 1
  ordered := zero_le_one
  curve t := UpperHalfPlane.mk
    ((x : ℂ) + (Real.exp (Real.log p + t * (Real.log q - Real.log p)) : ℂ) * Complex.I)
    (by simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using
      Real.exp_pos (Real.log p + t * (Real.log q - Real.log p)))
  velocity t :=
    ((Real.exp (Real.log p + t * (Real.log q - Real.log p)) *
      (Real.log q - Real.log p) : ℝ) : ℂ) * Complex.I
  continuous_curve := by
    apply Continuous.continuousOn
    apply Continuous.upperHalfPlaneMk
    fun_prop
  continuous_velocity := by fun_prop
  hasDerivWithin t _ := by
    have hlin : HasDerivAt (fun s : ℝ => Real.log p + s * (Real.log q - Real.log p))
        (Real.log q - Real.log p) t := by
      convert (hasDerivAt_id t).mul_const (Real.log q - Real.log p) |>.const_add (Real.log p) using 1 <;>
        simp
    have he := hlin.exp.ofReal_comp
    simpa only [UpperHalfPlane.coe_mk] using
      ((he.mul_const Complex.I).const_add (x : ℂ)).hasDerivWithinAt

theorem verticalPiece_start (x p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (verticalPiece x p q hp hq).curve 0 = UpperHalfPlane.mk ⟨x, p⟩ hp := by
  apply UpperHalfPlane.ext_re_im <;>
    simp only [verticalPiece, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero,
      Real.exp_log hp]

theorem verticalPiece_finish (x p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (verticalPiece x p q hp hq).curve 1 = UpperHalfPlane.mk ⟨x, q⟩ hq := by
  have hlog : Real.log p + 1 * (Real.log q - Real.log p) = Real.log q := by ring
  apply UpperHalfPlane.ext_re_im <;>
    simp only [verticalPiece, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_zero,
      hlog, Real.exp_log hq]

theorem verticalPiece_speed (x p q : ℝ) (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    weightedSpeed (verticalPiece x p q hp hq).curve (verticalPiece x p q hp hq).velocity t =
      |Real.log q - Real.log p| := by
  simp only [weightedSpeed, verticalPiece, UpperHalfPlane.mk_im, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, zero_mul, zero_add, add_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_I, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]

theorem verticalPiece_length (x p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (verticalPiece x p q hp hq).length = |Real.log q - Real.log p| := by
  unfold C1CurvePiece.length
  simp only [verticalPiece_speed]
  change (∫ _ : ℝ in (0 : ℝ)..1, |Real.log q - Real.log p|) = _
  simp

/-- Every pair of points has an actual C¹ curve attaining its hyperbolic distance. -/
theorem exists_length_minimizing_piece (z w : ℍ) :
    ∃ c : C1CurvePiece, c.curve c.a = z ∧ c.curve c.b = w ∧ c.length = dist z w := by
  obtain ⟨g, hg⟩ := exists_sl2_same_real_part z w
  let d := verticalPiece (g • z).re (g • z).im (g • w).im (g • z).im_pos (g • w).im_pos
  have hs : d.curve d.a = g • z := by
    change (verticalPiece _ _ _ _ _).curve 0 = _
    rw [verticalPiece_start]
    apply UpperHalfPlane.ext_re_im <;> rfl
  have hf : d.curve d.b = g • w := by
    change (verticalPiece _ _ _ _ _).curve 1 = _
    rw [verticalPiece_finish]
    apply UpperHalfPlane.ext_re_im
    · exact hg
    · rfl
  refine ⟨d.mapSL2 g⁻¹, ?_, ?_, ?_⟩
  · change g⁻¹ • d.curve d.a = z
    rw [hs, inv_smul_smul]
  · change g⁻¹ • d.curve d.b = w
    rw [hf, inv_smul_smul]
  · rw [d.mapSL2_length]
    change (verticalPiece _ _ _ _ _).length = _
    rw [verticalPiece_length, ← dist_smul g z w, UpperHalfPlane.dist_of_re_eq hg,
      Real.dist_eq, abs_sub_comm]

/-- A minimizing piece supplies the reverse inequality for the piecewise-curve infimum. -/
theorem piecewisePathEDist_le_metric (z w : ℍ) :
    piecewisePathEDist z w ≤ ENNReal.ofReal (dist z w) := by
  obtain ⟨c, rfl, rfl, hlen⟩ := exists_length_minimizing_piece z w
  have h := iInf_le (fun d : PiecewiseC1Curve (c.curve c.a) (c.curve c.b) =>
    ENNReal.ofReal d.length) (.cons c (.nil _))
  simpa only [piecewisePathEDist, _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length, add_zero,
    hlen] using h

/-- The metric from the geometric weighted piecewise C¹ lengths equals Mathlib's metric. -/
theorem piecewisePathEDist_eq_metric (z w : ℍ) :
    piecewisePathEDist z w = ENNReal.ofReal (dist z w) :=
  le_antisymm (piecewisePathEDist_le_metric z w) (metric_le_piecewisePathEDist z w)

/-- The real path distance obtained from the weighted length infimum. -/
@[expose] def piecewisePathDist (z w : ℍ) : ℝ := (piecewisePathEDist z w).toReal

theorem piecewisePathDist_eq_metric (z w : ℍ) : piecewisePathDist z w = dist z w := by
  rw [piecewisePathDist, piecewisePathEDist_eq_metric, ENNReal.toReal_ofReal dist_nonneg]

/-- The distance defined by weighted lengths satisfies all four metric requirements. -/
theorem path_distance_metric_axioms (z w u : ℍ) :
    0 ≤ piecewisePathDist z w ∧
    (piecewisePathDist z w = 0 ↔ z = w) ∧
    piecewisePathDist z w = piecewisePathDist w z ∧
    piecewisePathDist z u ≤ piecewisePathDist z w + piecewisePathDist w u := by
  simp only [piecewisePathDist_eq_metric]
  exact ⟨dist_nonneg, dist_eq_zero, dist_comm z w, dist_triangle z w u⟩

/-- The extended-infimum construction agrees with the ordinary real infimum in this formulation. -/
theorem piecewisePathDist_eq_sInf_lengths (z w : ℍ) :
    piecewisePathDist z w = sInf (Set.range (fun c : PiecewiseC1Curve z w => c.length)) := by
  obtain ⟨c, rfl, rfl, hlen⟩ := exists_length_minimizing_piece z w
  have hmem : dist (c.curve c.a) (c.curve c.b) ∈
      Set.range (fun d : PiecewiseC1Curve (c.curve c.a) (c.curve c.b) => d.length) := by
    exact ⟨.cons c (.nil _), by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length, add_zero] using hlen⟩
  have hbound : BddBelow
      (Set.range (fun d : PiecewiseC1Curve (c.curve c.a) (c.curve c.b) => d.length)) := by
    refine ⟨dist (c.curve c.a) (c.curve c.b), ?_⟩
    rintro _ ⟨d, rfl⟩
    exact d.dist_le_length
  rw [piecewisePathDist_eq_metric]
  apply le_antisymm
  · apply le_csInf ⟨_, hmem⟩
    rintro _ ⟨d, rfl⟩
    exact d.dist_le_length
  · exact csInf_le hbound hmem

/-- The five formulas, for the actual weighted path infimum. -/
theorem halfPlane_pathDist_log_cosh_sinh_tanh_formulas (z w : ℍ) :
    (piecewisePathDist z w = Real.log ((‖(z : ℂ) - conj (w : ℂ)‖ + ‖(z : ℂ) - w‖) /
      (‖(z : ℂ) - conj (w : ℂ)‖ - ‖(z : ℂ) - w‖))) ∧
    (Real.cosh (piecewisePathDist z w) = 1 + ‖(z : ℂ) - w‖ ^ 2 / (2 * z.im * w.im)) ∧
    (Real.sinh (piecewisePathDist z w / 2) = ‖(z : ℂ) - w‖ /
      (2 * Real.sqrt (z.im * w.im))) ∧
    (Real.cosh (piecewisePathDist z w / 2) = ‖(z : ℂ) - conj (w : ℂ)‖ /
      (2 * Real.sqrt (z.im * w.im))) ∧
    (Real.tanh (piecewisePathDist z w / 2) = ‖(z : ℂ) - w‖ /
      ‖(z : ℂ) - conj (w : ℂ)‖) := by
  simpa only [piecewisePathDist_eq_metric] using halfPlane_dist_log_cosh_sinh_tanh_formulas z w

/-- For determinant-one real Möbius maps. -/
theorem path_distance_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z w : ℍ) :
    piecewisePathDist (g • z) (g • w) = piecewisePathDist z w := by
  simpa only [piecewisePathDist_eq_metric] using dist_smul g z w

/-- without any ordering requirement on the positive heights. -/
theorem path_imaginary_axis_distance (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    piecewisePathDist (UpperHalfPlane.mk ⟨0, p⟩ hp) (UpperHalfPlane.mk ⟨0, q⟩ hq) =
      |Real.log (p / q)| := by
  rw [piecewisePathDist_eq_metric]
  exact metric_imaginary_axis_distance p q hp hq

end

end LowDimensionalTopology.Geometry.Hyperbolic
