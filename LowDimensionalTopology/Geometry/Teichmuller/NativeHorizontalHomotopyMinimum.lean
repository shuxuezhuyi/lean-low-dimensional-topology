module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedHorizontalArcShortest
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path

/-!
# Horizontal arcs in a fixed endpoint homotopy class

A finite native-length horizontal arc is no longer than the true quadratic
length of any original-surface path in its endpoint homotopy class. Both paths
are lifted from the same point, so the homotopy fixes their lifted endpoints.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- A horizontal arc of finite native length minimizes the quadratic length
of every homotopic original path, measured up to monotone reparametrization. -/
theorem nativeHorizontalArc_length_le_homotopic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p : UpperHalfPlane → X) (_hp : IsUniformization Γ p)
      (a b : X) (α β : Path a b),
      IsHorizontalArcRS (q : X → ℂ → ℂ) α →
      phiLengthPath (q : X → ℂ → ℂ) α < ⊤ →
      β.Homotopic α →
      phiLengthPath (q : X → ℂ → ℂ) α ≤
        phiLengthPathInv (q : X → ℂ → ℂ) β := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro Γ p hp a b α β hα hfin hβα
  obtain ⟨u₀, hu₀⟩ := hp.2.2.1 a
  have hα0 : (α : C(unitInterval, X)) 0 = p u₀ := by
    rw [hu₀]
    exact α.source
  let A : C(unitInterval, UpperHalfPlane) :=
    hp.1.liftPath (α : C(unitInterval, X)) u₀ hα0
  have hA0 : A 0 = u₀ :=
    hp.1.liftPath_zero (α : C(unitInterval, X)) u₀ hα0
  have hAlift : ∀ t, p (A t) = α t :=
    fun t => congrFun (hp.1.liftPath_lifts (α : C(unitInterval, X)) u₀ hα0) t
  have hc := utm_horizontal_lift q.property hp α hα A hAlift
  obtain ⟨-, hlenα⟩ := utm_length_lift q.property hp α A hAlift hfin
  let c : ℝ → ℂ := fun t => (A (Set.projIcc 0 1 zero_le_one t) : ℂ)
  have hcc : ContinuousOn c (Icc 0 1) := (utm_a_lift_continuous A).continuousOn
  have hcH : c '' Icc 0 1 ⊆ upperHalf := by
    rintro _ ⟨t, -, rfl⟩
    exact (A _).coe_im_pos
  unfold phiLengthPathInv
  refine le_iInf fun σ => le_iInf fun hσ => le_iInf fun h0 =>
    le_iInf fun h1 => le_iInf fun _ => ?_
  let γ : Path a b := β.reparam σ hσ h0 h1
  change phiLengthPath (q : X → ℂ → ℂ) α ≤ phiLengthPath (q : X → ℂ → ℂ) γ
  by_cases hγtop : phiLengthPath (q : X → ℂ → ℂ) γ = ⊤
  · rw [hγtop]
    exact le_top
  have hβγ : β.Homotopic γ := ⟨Path.Homotopy.reparam β σ hσ h0 h1⟩
  have hγα : γ.Homotopic α := hβγ.symm.trans hβα
  have hγ0 : (γ : C(unitInterval, X)) 0 = p u₀ := by
    rw [hu₀]
    exact γ.source
  let B : C(unitInterval, UpperHalfPlane) :=
    hp.1.liftPath (γ : C(unitInterval, X)) u₀ hγ0
  have hBlift : ∀ t, p (B t) = γ t :=
    fun t => congrFun (hp.1.liftPath_lifts (γ : C(unitInterval, X)) u₀ hγ0) t
  have hB0A0 : B 0 = A 0 :=
    (hp.1.liftPath_zero (γ : C(unitInterval, X)) u₀ hγ0).trans hA0.symm
  have hB1A1 : B 1 = A 1 := by
    exact hp.1.liftPath_apply_one_eq_of_homotopicRel hγα u₀ hγ0 hα0
  obtain ⟨⟨K, hK⟩, hlenγ⟩ :=
    utm_length_lift q.property hp γ B hBlift (lt_top_iff_ne_top.2 hγtop)
  let d : ℝ → ℂ := fun t => (B (Set.projIcc 0 1 zero_le_one t) : ℂ)
  let L : LRCurve := ⟨d, fun _ _ =>
    ⟨K, Ioo 0 1, self_mem_nhdsWithin, hK.mono Ioo_subset_Icc_self⟩⟩
  have hLH : L.trace ⊆ upperHalf := by
    rintro _ ⟨t, -, rfl⟩
    exact (B _).coe_im_pos
  have hd0 : d 0 = c 0 := by
    simp only [d, c, Set.projIcc_left]
    exact congrArg (fun z : UpperHalfPlane => (z : ℂ)) hB0A0
  have hd1 : d 1 = c 1 := by
    simp only [d, c, Set.projIcc_right]
    exact congrArg (fun z : UpperHalfPlane => (z : ℂ)) hB1A1
  have hLa : Tendsto L.toFun (nhdsWithin 0 (Ioi 0)) (𝓝 (c 0)) := by
    change Tendsto d (nhdsWithin 0 (Ioi 0)) (𝓝 (c 0))
    rw [← hd0]
    exact (utm_a_lift_continuous B).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hLb : Tendsto L.toFun (nhdsWithin 1 (Iio 1)) (𝓝 (c 1)) := by
    change Tendsto d (nhdsWithin 1 (Iio 1)) (𝓝 (c 1))
    rw [← hd1]
    exact (utm_a_lift_continuous B).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmin := nativeLiftedHorizontalArc_shortest R q hq Γ p hp c 0 1
    zero_lt_one hc hcc hcH L hLH hLa hLb
  have hlenL : phiLength (utm_liftQD (q : X → ℂ → ℂ) p) L =
      phiLengthPath (q : X → ℂ → ℂ) γ := by
    change (∫⁻ t in Ioo (0 : ℝ) 1,
      phiDensity (utm_liftQD (q : X → ℂ → ℂ) p) (d t) * ‖deriv d t‖ₑ) = _
    exact hlenγ
  calc
    phiLengthPath (q : X → ℂ → ℂ) α =
        ∫⁻ t in Ioo (0 : ℝ) 1,
          phiDensity (utm_liftQD (q : X → ℂ → ℂ) p) (c t) * ‖deriv c t‖ₑ := hlenα.symm
    _ ≤ phiLength (utm_liftQD (q : X → ℂ → ℂ) p) L := hmin
    _ = phiLengthPath (q : X → ℂ → ℂ) γ := hlenL

end LowDimensionalTopology.Geometry.Teichmuller
