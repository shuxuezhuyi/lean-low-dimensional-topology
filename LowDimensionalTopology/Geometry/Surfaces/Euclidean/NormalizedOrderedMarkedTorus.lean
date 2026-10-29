module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusModel
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Ordered standard markings of actual normalized complex tori

The loops are the projections of the literal segments from 0 to the two
specified periods. Marking compatibility is indexwise equality of their path
homotopy classes after one common basepoint-transport path. No arbitrary
choice of two generators is declared to be the standard marking.
-/

@[expose] public section
noncomputable section

open Set Module

namespace LowDimensionalTopology.Geometry.Surfaces

namespace ComplexTorusModel

variable {b c : Basis (Fin 2) ℝ ℂ}

/-- The genuine projected segment from 0 to a specified original lattice period. -/
def periodLoop (T : ComplexTorusModel b) (v : ℂ)
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    Path (T.projection 0) (T.projection 0) where
  toFun t := T.projection (t.val • v)
  continuous_toFun := T.covering.continuous.comp
    (continuous_subtype_val.smul continuous_const)
  source' := by simp
  target' := by
    change T.projection ((1 : ℝ) • v) = T.projection 0
    rw [one_smul]
    exact (T.fiber_iff v 0).mpr (by simpa only [sub_zero] using hv)

theorem projection_add_period (T : ComplexTorusModel b) (z v : ℂ)
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    T.projection (z + v) = T.projection z :=
  (T.fiber_iff (z + v) z).mpr (by simpa only [add_sub_cancel_left] using hv)

/-- Actual basepoint transport of a period loop forces equality of its affine
lift displacement. This is proved from covering monodromy, not assumed as a
property of a marking. -/
theorem affine_period_eq_of_marked_loop
    (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (f : ComplexTorusCarrier ≃ₜ ComplexTorusCarrier)
    (a d : ℂ) (hcomm : ∀ z : ℂ, f (T.projection z) = U.projection (a * z + d))
    (v w : ℂ) (hv : v ∈ Submodule.span ℤ (Set.range b))
    (hw : w ∈ Submodule.span ℤ (Set.range c))
    (C₀ : Path (f (T.projection 0)) (U.projection 0))
    (hmark : Path.Homotopic
      (((T.periodLoop v hv).map f.continuous).trans C₀)
      (C₀.trans (U.periodLoop w hw))) : a * v = w := by
  have hd : U.projection d = f (T.projection 0) := by
    simpa only [mul_zero, zero_add] using (hcomm 0).symm
  have hav : a * v ∈ Submodule.span ℤ (Set.range c) := by
    have hTv : T.projection v = T.projection 0 :=
      (T.fiber_iff v 0).mpr (by simpa only [sub_zero] using hv)
    have hUv : U.projection (a * v + d) = U.projection d :=
      (hcomm v).symm.trans ((congrArg f hTv).trans hd.symm)
    simpa only [add_sub_cancel_right] using (U.fiber_iff (a * v + d) d).mp hUv
  let e : U.projection ⁻¹' {f (T.projection 0)} := ⟨d, hd⟩
  let L₁ : C(unitInterval, ℂ) :=
    ⟨fun t => a * (t.val • v) + d, by fun_prop⟩
  have hL₁ : U.projection ∘ L₁ = (T.periodLoop v hv).map f.continuous := by
    funext t
    exact (hcomm (t.val • v)).symm
  let e₁ := U.covering.monodromy
    (Path.Homotopic.Quotient.mk ((T.periodLoop v hv).map f.continuous)) e
  have he₁ : (e₁ : ℂ) = a * v + d := by
    have h := U.covering.monodromy_eq_apply_one (e := e) (Γ := L₁)
      hL₁ (by simp [L₁, e])
    simpa only [L₁, ContinuousMap.coe_mk, Set.Icc.coe_one, one_smul] using h
  obtain ⟨C, hC, hC₀⟩ := U.covering.exists_path_lifts
    (C₀ : C(unitInterval, ComplexTorusCarrier)) d (C₀.source.trans hd.symm)
  let eC := U.covering.monodromy (Path.Homotopic.Quotient.mk C₀) e
  have heC : (eC : ℂ) = C 1 :=
    U.covering.monodromy_eq_apply_one hC hC₀
  have heCperiod : (eC : ℂ) ∈ Submodule.span ℤ (Set.range c) := by
    simpa only [sub_zero] using (U.fiber_iff (eC : ℂ) 0).mp eC.property
  let L₂ : C(unitInterval, ℂ) :=
    ⟨fun t => t.val • w + (eC : ℂ), by fun_prop⟩
  have hL₂ : U.projection ∘ L₂ = U.periodLoop w hw := by
    funext t
    exact U.projection_add_period (t.val • w) (eC : ℂ) heCperiod
  have hmon₂ :
      (U.covering.monodromy (Path.Homotopic.Quotient.mk (U.periodLoop w hw)) eC : ℂ) =
        w + (eC : ℂ) := by
    have h := U.covering.monodromy_eq_apply_one (e := eC) (Γ := L₂)
      hL₂ (by simp [L₂])
    simpa only [L₂, ContinuousMap.coe_mk, Set.Icc.coe_one, one_smul] using h
  let C' : C(unitInterval, ℂ) := ⟨fun t => C t + a * v, C.continuous.add continuous_const⟩
  have hC' : U.projection ∘ C' = C₀ := by
    funext t
    exact (U.projection_add_period (C t) (a * v) hav).trans (congrFun hC t)
  have hC'₀ : C' 0 = (e₁ : ℂ) := by
    change C 0 + a * v = (e₁ : ℂ)
    rw [hC₀, he₁]
    exact add_comm _ _
  have hmonC' :
      (U.covering.monodromy (Path.Homotopic.Quotient.mk C₀) e₁ : ℂ) = C 1 + a * v :=
    U.covering.monodromy_eq_apply_one hC' hC'₀
  have hpaths := Path.Homotopic.Quotient.eq.mpr hmark
  have hend := congrArg
    (fun P : Path.Homotopic.Quotient (f (T.projection 0)) (U.projection 0) =>
      (U.covering.monodromy P e : ℂ)) hpaths
  simp only [Path.Homotopic.Quotient.mk_trans, U.covering.monodromy_trans_apply] at hend
  change (U.covering.monodromy (Path.Homotopic.Quotient.mk C₀) e₁ : ℂ) =
    (U.covering.monodromy (Path.Homotopic.Quotient.mk (U.periodLoop w hw)) eC : ℂ) at hend
  rw [hmonC', hmon₂, ← heC] at hend
  exact add_left_cancel (hend.trans (add_comm w (eC : ℂ)))

end ComplexTorusModel

/-- The specified ordered standard loops: index zero has period 1, index one has
period τ, through the original normalized basis and covering. -/
def normalizedTorusMarkingLoop (τ : UpperHalfPlane) (i : Fin 2) :
    Path ((normalizedTorusModel τ).projection 0) ((normalizedTorusModel τ).projection 0) :=
  (normalizedTorusModel τ).periodLoop (normalizedTorusBasis τ i)
    (Submodule.subset_span (Set.mem_range_self i))

/-- Equality of the actual ordered standard marked tori, allowing the book's
single common basepoint-transport path. The homotopy equation is the path
groupoid form of equality of the two transported fundamental-group classes. -/
def NormalizedOrderedMarkedEquivalent (τ σ : UpperHalfPlane) : Prop :=
  ∃ f : ComplexTorusCarrier ≃ₜ ComplexTorusCarrier,
    RiemannAnalyticMap (normalizedTorusModel τ).surface.toRiemannAtlas
      (normalizedTorusModel σ).surface.toRiemannAtlas f ∧
    ∃ C : Path (f ((normalizedTorusModel τ).projection 0))
        ((normalizedTorusModel σ).projection 0),
      ∀ i : Fin 2, Path.Homotopic
        (((normalizedTorusMarkingLoop τ i).map f.continuous).trans C)
        (C.trans (normalizedTorusMarkingLoop σ i))

/-- The actual ordered standard marked tori have equal parameters exactly when
they are equivalent by an analytic target homeomorphism and basepoint transport. -/
theorem normalizedOrderedMarkedEquivalent_iff (τ σ : UpperHalfPlane) :
    NormalizedOrderedMarkedEquivalent τ σ ↔ τ = σ := by
  constructor
  · rintro ⟨f, hf, C, hC⟩
    obtain ⟨a, d, _ha, hcomm⟩ :=
      (normalizedTorusModel τ).analytic_homeomorph_has_affine_lift
        (normalizedTorusModel σ) f hf
    have ha : a = 1 := by
      have h := (normalizedTorusModel τ).affine_period_eq_of_marked_loop
        (normalizedTorusModel σ) f a d hcomm
        (normalizedTorusBasis τ 0) (normalizedTorusBasis σ 0)
        (Submodule.subset_span (Set.mem_range_self 0))
        (Submodule.subset_span (Set.mem_range_self 0)) C (hC 0)
      simpa only [normalizedTorusBasis_zero, mul_one] using h
    have hτσ := (normalizedTorusModel τ).affine_period_eq_of_marked_loop
      (normalizedTorusModel σ) f a d hcomm
      (normalizedTorusBasis τ 1) (normalizedTorusBasis σ 1)
      (Submodule.subset_span (Set.mem_range_self 1))
      (Submodule.subset_span (Set.mem_range_self 1)) C (hC 1)
    apply UpperHalfPlane.ext
    simpa only [normalizedTorusBasis_one, ha, one_mul] using hτσ
  · intro h
    subst σ
    refine ⟨Homeomorph.refl _, RiemannAnalyticMap.id _, Path.refl _, ?_⟩
    intro i
    have hid : (normalizedTorusMarkingLoop τ i).map (Homeomorph.refl _).continuous =
        normalizedTorusMarkingLoop τ i := by
      apply Path.ext
      funext t
      rfl
    rw [hid]
    exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans _).symm

end LowDimensionalTopology.Geometry.Surfaces
