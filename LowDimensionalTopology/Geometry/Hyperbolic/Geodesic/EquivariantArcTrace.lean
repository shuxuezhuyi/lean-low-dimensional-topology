module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.EquivariantAxisUniqueness
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AxisPeriodicGeodesic
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import Mathlib.Algebra.Field.Periodic

/-!
# Actual equivariant arc traces determine the full projected axis

No speed or absolute continuity is imposed on the given continuous local arc.
Two distinct points show that its complete supporting line is invariant under
the actual deck matrix. Native hyperbolic axis uniqueness then identifies that
line. The intermediate value theorem on one actual period, followed by actual
periodicity, proves that its projected trace is the entire projected axis.
The matrix and its full period are retained, including proper powers.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem range_comp_eq_of_period_endpoint
    {Y : Type*} (F : ℝ → Y) {c : ℝ} (hF : Function.Periodic F c) (hc : c ≠ 0)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (T : ℝ) (hend : κ T = κ 0 + c) :
    range (F ∘ κ) = range F := by
  apply subset_antisymm (range_comp_subset_range _ _)
  have hperiod : F '' uIcc (κ 0) (κ T) = range F := by
    rw [hend]
    exact hF.image_uIcc hc (κ 0)
  rintro y hy
  obtain ⟨u, hu, huy⟩ := hperiod.symm ▸ hy
  obtain ⟨t, _ht, htu⟩ := intermediate_value_uIcc hκ.continuousOn hu
  exact ⟨t, (congrArg F htu).trans huy⟩

/-- A genuine continuous locally injective arc with a complete supporting line
and an actual hyperbolic deck period lies on that same matrix's actual axis.
Only the arc data supply nondegeneracy; no original unit-speed premise occurs. -/
theorem equivariant_arc_supporting_line_eq_axis
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    {f : ℝ → ℍ} (hfinj : IsLocallyInjective f)
    {S : Set ℍ} (hS : IsHalfPlaneHLine S) (hfS : range f ⊆ S)
    (T : ℝ) (hperiod : ∀ t : ℝ, f (t + T) = A • f t) :
    S = (hHyperbolicAxis A hA ht).carrier := by
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hS
  have his : Isometry (fun z : ℍ => A • z) := isometry_smul ℍ A
  obtain ⟨N, hN⟩ :=
    LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine his L
  obtain ⟨U, hUopen, hzeroU, hUinj⟩ := hfinj 0
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hzeroU)
  have hhalfU : ε / 2 ∈ U := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hne : f 0 ≠ f (ε / 2) := by
    intro he
    have heq := hUinj hzeroU hhalfU he
    linarith
  have himage (t : ℝ) : f t ∈ (fun z : ℍ => A • z) '' L.carrier := by
    refine ⟨f (t - T), hL.symm ▸ hfS (mem_range_self _), ?_⟩
    simpa only [sub_add_cancel] using (hperiod (t - T)).symm
  have hsame : L.carrier = N.carrier :=
    isHLine_eq_of_two_points L.isHLine N.isHLine hne
      (hL.symm ▸ hfS (mem_range_self 0)) (hL.symm ▸ hfS (mem_range_self (ε / 2)))
      (hN ▸ himage 0) (hN ▸ himage (ε / 2))
  have hinv : (fun z : ℍ => A • z) '' L.carrier = L.carrier := hN.trans hsame.symm
  exact hL.symm.trans (congrArg HalfPlaneLine.carrier
    (hHyperbolicAxis_unique_invariant A hA ht L hinv))

/-- The full unparametrized projected trace of an actual equivariant local arc
is the full projected native axis. The intermediate value argument retains
arbitrary singular parameters allowed by the arc hypotheses. -/
theorem equivariant_arc_projected_trace_eq_axis
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    {f : ℝ → ℍ} (hf : Continuous f) (hfinj : IsLocallyInjective f)
    {S : Set ℍ} (hS : IsHalfPlaneHLine S) (hfS : range f ⊆ S)
    (T : ℝ) (hperiod : ∀ t : ℝ, f (t + T) = A • f t) :
    range (p ∘ f) = p '' (hHyperbolicAxis A hA ht).carrier := by
  have haxis := equivariant_arc_supporting_line_eq_axis A hA ht hfinj hS hfS T hperiod
  obtain ⟨γ, hγ, hγaxis, hlength, hγperiod⟩ := exists_unitSpeed_axis_with_actual_period A hA ht
  have hfrange (t : ℝ) : f t ∈ range γ :=
    hγaxis.symm ▸ (haxis ▸ hfS (mem_range_self t))
  let e := hγ.1.isometryEquivOnRange
  let κ : ℝ → ℝ := fun t => e.symm ⟨f t, hfrange t⟩
  have hκ : Continuous κ := e.symm.continuous.comp (hf.subtype_mk hfrange)
  have hpoint (t : ℝ) : γ (κ t) = f t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f t, hfrange t⟩)
  have hend : κ T = κ 0 + hTranslationLength (hSLIsometry A) := by
    apply hγ.1.injective
    rw [hpoint, hγperiod, hpoint]
    simpa only [zero_add] using hperiod 0
  have hprojected : Function.Periodic (p ∘ γ) (hTranslationLength (hSLIsometry A)) := by
    intro t
    change p (γ (t + hTranslationLength (hSLIsometry A))) = p (γ t)
    rw [hγperiod, LiZhongQC.s30a_p_smul hp hAΓ]
  have hcomp : p ∘ f = (p ∘ γ) ∘ κ := by
    funext t
    change p (f t) = p (γ (κ t))
    rw [hpoint]
  rw [hcomp, range_comp_eq_of_period_endpoint (p ∘ γ) hprojected hlength.ne' κ hκ T hend,
    range_comp, hγaxis]

end LowDimensionalTopology.Geometry.Hyperbolic
