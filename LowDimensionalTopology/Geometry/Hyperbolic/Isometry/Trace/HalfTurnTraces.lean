/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Trace.TriangleInvariant
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicHalfTurns
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The exact three-factor trace identity for arbitrary genuine traceless real two-by-two matrices. -/
theorem traceless_matrix_triple_trace (A B C : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : Matrix.trace A=0) (hB : Matrix.trace B=0) (hC : Matrix.trace C=0) :
    (Matrix.trace (A*B*C))^2=4*A.det*B.det*C.det-
      A.det*(Matrix.trace (B*C))^2-B.det*(Matrix.trace (C*A))^2-
      C.det*(Matrix.trace (A*B))^2-
      Matrix.trace (A*B)*Matrix.trace (B*C)*Matrix.trace (C*A) := by
  have ha : A 1 1= -A 0 0 := by rw [Matrix.trace_fin_two] at hA;linarith
  have hb : B 1 1= -B 0 0 := by rw [Matrix.trace_fin_two] at hB;linarith
  have hc : C 1 1= -C 0 0 := by rw [Matrix.trace_fin_two] at hC;linarith
  simp only [Matrix.trace_fin_two,Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_two,ha,hb,hc]
  ring

theorem traceless_realSL_triple_trace (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Matrix.trace A.val=0) (hB : Matrix.trace B.val=0) (hC : Matrix.trace C.val=0) :
    (Matrix.trace (A*B*C).val)^2=4-(Matrix.trace (B*C).val)^2-
      (Matrix.trace (C*A).val)^2-(Matrix.trace (A*B).val)^2-
      Matrix.trace (A*B).val*Matrix.trace (B*C).val*Matrix.trace (C*A).val := by
  have he:=traceless_matrix_triple_trace A.val B.val C.val hA hB hC
  rw [A.det_coe,B.det_coe,C.det_coe] at he
  simpa only [Matrix.SpecialLinearGroup.coe_mul,mul_one,one_mul] using he

/-- A literal determinant-one half-turn matrix for every actual native center. -/
def pointHalfTurnSL (z : ℍ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![z.re/z.im,-(z.re^2+z.im^2)/z.im;1/z.im,-z.re/z.im],by
    rw [Matrix.det_fin_two]
    dsimp
    field_simp [z.im_ne_zero]
    ring⟩

theorem pointHalfTurnSL_trace (z : ℍ) : Matrix.trace (pointHalfTurnSL z).val=0 := by
  simp [pointHalfTurnSL,Matrix.trace_fin_two]
  ring

theorem pointHalfTurnSL_fixed (z : ℍ) : pointHalfTurnSL z•z=z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  have hd:=UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ (pointHalfTurnSL z)) z
  apply (div_eq_iff hd).mpr
  change (((z.re/z.im : ℝ):ℂ)*(z:ℂ)+((-(z.re^2+z.im^2)/z.im : ℝ):ℂ))=
    (z:ℂ)*((((1/z.im : ℝ):ℂ)*(z:ℂ))+((-z.re/z.im : ℝ):ℂ))
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]
  apply Complex.ext <;> simp [pow_two,Complex.mul_re,Complex.mul_im]

theorem pointHalfTurnSL_at (z : ℍ) : IsHalfTurnAt (pointHalfTurnSL z) z :=
  ⟨(realSLMobius_order_two_iff_trace_zero _
    (realSL_trace_zero_ne_one _ (pointHalfTurnSL_trace z))).mpr (pointHalfTurnSL_trace z),
    pointHalfTurnSL_fixed z⟩

/-- The coherently oriented true half-turn matrices have the signed actual distance trace. -/
theorem pointHalfTurnSL_pair_trace (z w : ℍ) :
    Matrix.trace (pointHalfTurnSL z*pointHalfTurnSL w).val= -2*Real.cosh (dist z w) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  rw [UpperHalfPlane.cosh_dist']
  simp only [pointHalfTurnSL,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Matrix.of_apply]
  field_simp [z.im_ne_zero,w.im_ne_zero]
  ring

/-- The trace square is four times the genuine metric triangle discriminant. -/
theorem pointHalfTurnSL_triple_trace_sq (T : HTriangle) :
    (Matrix.trace (pointHalfTurnSL T.a*pointHalfTurnSL T.b*pointHalfTurnSL T.c).val)^2=
      4*(halfTurnTriangleInvariant T)^2 := by
  rw [traceless_realSL_triple_trace _ _ _ (pointHalfTurnSL_trace T.a)
    (pointHalfTurnSL_trace T.b) (pointHalfTurnSL_trace T.c)]
  rw [pointHalfTurnSL_pair_trace,pointHalfTurnSL_pair_trace,pointHalfTurnSL_pair_trace,
    halfTurnTriangleInvariant_sq]
  change 4-(-2*Real.cosh T.lengthA)^2-(-2*Real.cosh T.lengthB)^2-
    (-2*Real.cosh T.lengthC)^2-(-2*Real.cosh T.lengthC)*(-2*Real.cosh T.lengthA)*
      (-2*Real.cosh T.lengthB)=4*hyperbolicTriangleDiscriminant T.lengthA T.lengthB T.lengthC
  dsimp only [hyperbolicTriangleDiscriminant]
  ring

theorem pointHalfTurnSL_triple_abs_trace (T : HTriangle) :
    |Matrix.trace (pointHalfTurnSL T.a*pointHalfTurnSL T.b*pointHalfTurnSL T.c).val|=
      2*halfTurnTriangleInvariant T := by
  apply (sq_eq_sq₀ (abs_nonneg _) (by positivity [halfTurnTriangleInvariant_pos T])).mp
  rw [sq_abs,pointHalfTurnSL_triple_trace_sq]
  ring

/-- The primary source trace formula for arbitrary true half-turn lifts and true centers. -/
theorem halfTurn_triple_abs_trace (T : HTriangle) (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : IsHalfTurnAt A T.a) (hB : IsHalfTurnAt B T.b) (hC : IsHalfTurnAt C T.c) :
    |Matrix.trace (A*B*C).val|=2*halfTurnTriangleInvariant T := by
  calc
    _=Mobius.mobiusTraceAbs (realSLMobius (A*B*C)) := (realSLMobius_traceAbs _).symm
    _=Mobius.mobiusTraceAbs (realSLMobius (pointHalfTurnSL T.a*pointHalfTurnSL T.b*pointHalfTurnSL T.c)) := by
      simp only [map_mul]
      rw [hA.unique (pointHalfTurnSL_at T.a),hB.unique (pointHalfTurnSL_at T.b),
        hC.unique (pointHalfTurnSL_at T.c)]
    _=_ := (realSLMobius_traceAbs _).trans (pointHalfTurnSL_triple_abs_trace T)

theorem realSL_triple_trace_cycle (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A*B*C).val=Matrix.trace (C*A*B).val := by
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using Matrix.trace_mul_cycle A.val B.val C.val

/-- Reversal negates the genuine three-factor trace for traceless real lifts. -/
theorem realSL_traceless_triple_trace_reverse (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Matrix.trace A.val=0) (hB : Matrix.trace B.val=0) (hC : Matrix.trace C.val=0) :
    Matrix.trace (A*B*C).val= -Matrix.trace (C*B*A).val := by
  have ha : A 1 1= -A 0 0 := by rw [Matrix.trace_fin_two] at hA;linarith
  have hb : B 1 1= -B 0 0 := by rw [Matrix.trace_fin_two] at hB;linarith
  have hc : C 1 1= -C 0 0 := by rw [Matrix.trace_fin_two] at hC;linarith
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.trace_fin_two,Matrix.mul_apply,
    Fin.sum_univ_two,ha,hb,hc]
  ring

/-- The half-turn trace identity includes every one of the six actual permutation products. -/
theorem halfTurn_six_product_orders_abs_trace_eq_twice_triangleInvariant (T : HTriangle) (A B C :
  Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : IsHalfTurnAt A T.a) (hB : IsHalfTurnAt B T.b) (hC : IsHalfTurnAt C T.c) :
    |Matrix.trace (A*B*C).val|=2*halfTurnTriangleInvariant T ∧
    |Matrix.trace (C*A*B).val|=2*halfTurnTriangleInvariant T ∧
    |Matrix.trace (B*C*A).val|=2*halfTurnTriangleInvariant T ∧
    |Matrix.trace (C*B*A).val|=2*halfTurnTriangleInvariant T ∧
    |Matrix.trace (A*C*B).val|=2*halfTurnTriangleInvariant T ∧
    |Matrix.trace (B*A*C).val|=2*halfTurnTriangleInvariant T := by
  have ha := (realSLMobius_order_two_iff_trace_zero A hA.ne_one).mp hA.1
  have hb := (realSLMobius_order_two_iff_trace_zero B hB.ne_one).mp hB.1
  have hc := (realSLMobius_order_two_iff_trace_zero C hC.ne_one).mp hC.1
  have hmain:=halfTurn_triple_abs_trace T A B C hA hB hC
  refine ⟨hmain,?_,?_,?_,?_,?_⟩
  · rw [←realSL_triple_trace_cycle A B C]
    exact hmain
  · rw [realSL_triple_trace_cycle B C A]
    exact hmain
  · rw [realSL_traceless_triple_trace_reverse C B A hc hb ha,abs_neg]
    exact hmain
  · rw [realSL_traceless_triple_trace_reverse A C B ha hc hb,
      realSL_triple_trace_cycle B C A,abs_neg]
    exact hmain
  · rw [realSL_traceless_triple_trace_reverse B A C hb ha hc,
      ←realSL_triple_trace_cycle A B C,abs_neg]
    exact hmain

/-- Every actual half-plane-preserving geometric half-turn constructs its true real lift. -/
theorem geometric_halfTurn_lift_exists (f : Mobius.complexMobiusGroup) (p : ℍ)
    (hpres : f.val '' openHalfPlaneSet=openHalfPlaneSet)
    (ho : orderOf f=2) (hfix : f.val (p:ℂ)=(p:ℂ)) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, realSLMobius A=f ∧ IsHalfTurnAt A p := by
  obtain ⟨A,hA⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL f hpres
  refine ⟨A,hA,?_,?_⟩
  · rwa [hA]
  · apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [←realSLMobius_action,hA]
    exact hfix

/-- The same complete six-product theorem for the original geometric transformations;
their real lifts are conclusions, never extra representation assumptions. -/
theorem mobius_halfTurn_six_product_orders_abs_trace_eq_twice_triangleInvariant (T : HTriangle) (f g h :
  Mobius.complexMobiusGroup)
    (hf : f.val '' openHalfPlaneSet=openHalfPlaneSet)
    (hg : g.val '' openHalfPlaneSet=openHalfPlaneSet)
    (hh : h.val '' openHalfPlaneSet=openHalfPlaneSet)
    (hf2 : orderOf f=2) (hg2 : orderOf g=2) (hh2 : orderOf h=2)
    (hfa : f.val (T.a:ℂ)=(T.a:ℂ)) (hgb : g.val (T.b:ℂ)=(T.b:ℂ))
    (hhc : h.val (T.c:ℂ)=(T.c:ℂ)) :
    Mobius.mobiusTraceAbs (f*g*h)=2*halfTurnTriangleInvariant T ∧
    Mobius.mobiusTraceAbs (h*f*g)=2*halfTurnTriangleInvariant T ∧
    Mobius.mobiusTraceAbs (g*h*f)=2*halfTurnTriangleInvariant T ∧
    Mobius.mobiusTraceAbs (h*g*f)=2*halfTurnTriangleInvariant T ∧
    Mobius.mobiusTraceAbs (f*h*g)=2*halfTurnTriangleInvariant T ∧
    Mobius.mobiusTraceAbs (g*f*h)=2*halfTurnTriangleInvariant T := by
  obtain ⟨A,hA,hAt⟩:=geometric_halfTurn_lift_exists f T.a hf hf2 hfa
  obtain ⟨B,hB,hBt⟩:=geometric_halfTurn_lift_exists g T.b hg hg2 hgb
  obtain ⟨C,hC,hCt⟩:=geometric_halfTurn_lift_exists h T.c hh hh2 hhc
  simpa only [←hA,←hB,←hC,←map_mul,realSLMobius_traceAbs] using
    halfTurn_six_product_orders_abs_trace_eq_twice_triangleInvariant T A B C hAt hBt hCt

end LowDimensionalTopology.Geometry.Hyperbolic
