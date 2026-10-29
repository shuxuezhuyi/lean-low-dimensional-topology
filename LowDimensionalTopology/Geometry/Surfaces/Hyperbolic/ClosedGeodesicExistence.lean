module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AxisPeriodicGeodesic
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ClosedAxisMinimizer
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableFreeClass

/-!
# Closed geodesic representatives of arbitrary nontrivial loops

The loop is given on the original compact hyperbolic surface. Its actual
covering matrix, hyperbolicity, periodic geodesic and free homotopy are derived
from that loop and the original model. No covering matrix or alternate
uniformization is added to the hypotheses. The complete period retains proper
powers.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- The constant loop at a specified point of the surface. -/
@[expose] def constantLoop {X : Type*} [TopologicalSpace X] (x : X) : LiZhongQC.Loop X :=
  ⟨x, Path.refl x⟩

/-- A loop is freely null-homotopic when it is freely homotopic to a constant
loop. The base point of the constant loop is allowed to vary. -/
@[expose] def IsNullHomotopicLoop {X : Type*} [TopologicalSpace X]
    (α : LiZhongQC.Loop X) : Prop :=
  ∃ x : X, LiZhongQC.FreelyHomotopic α (constantLoop x)

private theorem nullHomotopic_of_trivial_cover
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : A ∈ Γ)
    {α : LiZhongQC.Loop X} (hcov : LiZhongQC.Covers p A α)
    (htrivial : ∀ z : ℍ, A • z = z) : IsNullHomotopicLoop α := by
  let e : C(I, ℍ) := ContinuousMap.const I UpperHalfPlane.I
  have he : e 1 = A • e 0 := (htrivial UpperHalfPlane.I).symm
  exact ⟨p UpperHalfPlane.I,
    LiZhongQC.s30a_fh_bwd hp hA hcov e he (constantLoop (p UpperHalfPlane.I))
      (fun _ => rfl)⟩

theorem exists_hyperbolic_cover_of_not_null
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p) (α : LiZhongQC.Loop X)
    (hnon : ¬ IsNullHomotopicLoop α) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      A ∈ Γ ∧ LiZhongQC.Covers p A α ∧ LiZhongQC.IsHyperbolic A ∧
      realSLMobius A ≠ 1 ∧ 4 < (Matrix.trace A.val) ^ 2 := by
  obtain ⟨A, hA, hcov⟩ := LiZhongQC.s30a_exists_covers hp α
  have h1 : A ≠ 1 := by
    intro he
    apply hnon (nullHomotopic_of_trivial_cover hp hA hcov ?_)
    intro z
    rw [he, one_smul]
  have hm1 : A ≠ -1 := by
    intro he
    apply hnon (nullHomotopic_of_trivial_cover hp hA hcov ?_)
    intro z
    rw [he, LiZhongQC.s27g_neg_one_smul]
  have hhyper : LiZhongQC.IsHyperbolic A := LiZhongQC.s27f_hyp hp hA h1 hm1
  have habs : 2 < |Matrix.trace A.val| := by
    simpa only [LiZhongQC.IsHyperbolic, LiZhongQC.slTrace, Matrix.trace_fin_two] using hhyper
  have ht : 4 < (Matrix.trace A.val) ^ 2 := by
    nlinarith [sq_abs (Matrix.trace A.val)]
  have hprojective : realSLMobius A ≠ 1 := by
    intro he
    have hidentity : mobiusSquaredTrace (1 : complexMobiusGroup) = (4 : ℂ) := by
      have hh := realSLMobius_squaredTrace (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      norm_num [Matrix.trace_fin_two] at hh
      exact hh
    have hh := congrArg mobiusSquaredTrace he
    rw [realSLMobius_squaredTrace, hidentity] at hh
    have hr : (Matrix.trace A.val) ^ 2 = 4 := Complex.ofReal_injective hh
    linarith
  exact ⟨A, hA, hcov, hhyper, hprojective, ht⟩

/-- Every nontrivial loop on the original compact hyperbolic surface has a
freely homotopic closed representative obtained from an actual complete
unit-speed geodesic. Its positive period is the infimum over all continuous
rectifiable lifts of loops in the original free homotopy class. -/
theorem HyperbolicSurfaceModel.exists_closed_geodesic_of_not_null
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : LiZhongQC.Loop X)
    (hnon : ¬ IsNullHomotopicLoop α) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ (β : LiZhongQC.Loop X) (γ : ℝ → ℍ) (T : ℝ),
      IsHGeodesicParam γ ∧ 0 < T ∧
      (∀ t : ℝ, M.halfPlaneCover (γ (t + T)) = M.halfPlaneCover (γ t)) ∧
      (∀ t : I, β.2 t = M.halfPlaneCover (γ (T * (t : ℝ)))) ∧
      LiZhongQC.FreelyHomotopic α β ∧
      rectifiableFreeHomotopyLength M.halfPlaneCover α = ENNReal.ofReal T := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hA, hcov, hhyper, hprojective, ht⟩ :=
    exists_hyperbolic_cover_of_not_null hp α hnon
  obtain ⟨γ, hγ, _hrange, hpositive, hperiod⟩ :=
    exists_unitSpeed_axis_with_actual_period A hprojective ht
  let T : ℝ := hTranslationLength (hSLIsometry A)
  let d : C(I, ℍ) :=
    ⟨fun t => γ (T * (t : ℝ)),
      hγ.1.continuous.comp (continuous_const.mul continuous_subtype_val)⟩
  have hd : d 1 = A • d 0 := by
    change γ (T * ((1 : I) : ℝ)) = A • γ (T * ((0 : I) : ℝ))
    simpa only [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, zero_add] using hperiod 0
  have hclosed : M.halfPlaneCover (d 1) = M.halfPlaneCover (d 0) := by
    rw [hd, LiZhongQC.s30a_p_smul hp hA]
  let β : LiZhongQC.Loop X :=
    LiZhongQC.s30a_projLoop M.halfPlaneCover hp.1.continuous d hclosed
  have hhom : LiZhongQC.FreelyHomotopic α β :=
    LiZhongQC.s30a_fh_bwd hp hA hcov d hd β (fun _ => rfl)
  have hlength : rectifiableFreeHomotopyLength M.halfPlaneCover α = ENNReal.ofReal T := by
    rw [rectifiableFreeHomotopyLength_eq_source M.halfPlaneCover hp.1.continuous α,
      LiZhongQC.s30a_len_hyp hp hA hhyper hcov,
      liZhong_translationLength_eq_native A hhyper]
  refine ⟨β, γ, T, hγ, hpositive, ?_, fun _ => rfl, hhom, hlength⟩
  intro t
  rw [hperiod, LiZhongQC.s30a_p_smul hp hA]

/-- The same arbitrary nontrivial free class has a native closed C1 minimizer
on the original surface. The actual loop, native C1 curve and literal minimum
agree; the minimizing curve is not supplied as an extra hypothesis. -/
theorem HyperbolicSurfaceModel.exists_closed_c1_minimizer_of_not_null
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : LiZhongQC.Loop X)
    (hnon : ¬ IsNullHomotopicLoop α) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ (β : LiZhongQC.Loop X) (q : HyperbolicSurfaceC1CurvePiece M),
      LiZhongQC.FreelyHomotopic α β ∧
      (∀ t : I, q.curve t = β.2 t) ∧ q.curve 1 = q.curve 0 ∧ 0 < q.length ∧
      LiZhongQC.poincareLengthLoop M.halfPlaneCover β = ENNReal.ofReal q.length ∧
      rectifiableFreeHomotopyLength M.halfPlaneCover α = ENNReal.ofReal q.length := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hA, hcov, _hhyper, hprojective, ht⟩ :=
    exists_hyperbolic_cover_of_not_null hp α hnon
  obtain ⟨β, q, _d, hcovβ, _ha, _hb, _haxis, _hperiod, _hproj, hpoint,
    hclosed, hlen, hloop, hfree, _htrace⟩ :=
    M.exists_closed_axis_c1_minimizer A ((hΓ A).1 hA) hprojective ht
  have hhom : LiZhongQC.FreelyHomotopic α β :=
    LiZhongQC.s30a_fh_of_conj hp hA (Γ.one_mem)
      (fun z => by simp only [one_mul, inv_one, mul_one]) hcov hcovβ
  have hpositive : 0 < q.length := by
    rw [hlen]
    exact hHyperbolic_translationLength_pos A hprojective ht
  have hlength :
      rectifiableFreeHomotopyLength M.halfPlaneCover α = ENNReal.ofReal q.length := by
    rw [rectifiableFreeHomotopyLength_eq_source M.halfPlaneCover hp.1.continuous α,
      LiZhongQC.s30b_fhl_congr M.halfPlaneCover hhom]
    exact hfree
  exact ⟨β, q, hhom, hpoint, hclosed, hpositive, hloop, hlength⟩

end LowDimensionalTopology.Geometry.Surfaces
