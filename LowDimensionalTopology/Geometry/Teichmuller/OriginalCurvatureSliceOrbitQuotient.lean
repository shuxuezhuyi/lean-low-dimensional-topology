module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalHyperbolicMetricConformalNormalization
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCurvatureSliceScaleTwo
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricStrongQuotientRealization

/-!
# The actual negative-curvature slice and its Diff0 orbit quotient

The relation is literal equality under the existing native smooth pullback.
Classical normalization removes the exponential factor from a strong raw
equivalence between two actual curvature-minus-one metrics. Inclusion of the
slice orbit quotient then gives the original all-raw strong quotient map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u v
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem curvatureMinusOne_strong_iff_pullback_orbit
    (hreg : Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (hcurv : Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature.{u})
    (hcov : Unproved.Teichmuller.OriginalMetricGaussianCurvatureCovariance.{u})
    (hnorm : Unproved.Teichmuller.OriginalHyperbolicMetricConformalNormalization.{u})
    {genus : ℕ} (hgenus : R.HasGenus genus) (hg : 1 < genus)
    (g h : ↥(curvatureMinusOneMetrics R hreg hcurv)) :
    RawMetricStronglyEquivalent R g.val h.val ↔
      ∃ f : OrientedSurfaceAut.homotopyIdentitySubgroup R,
        SmoothSurfaceMetric.pullback f.val.smooth h.val = g.val := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have haction : ∀ (f : OrientedSurfaceAut.homotopyIdentitySubgroup R)
      (m : SmoothSurfaceMetric R.toRiemannSurface),
      m ∈ curvatureMinusOneMetrics R hreg hcurv →
        SmoothSurfaceMetric.pullback f.val.smooth m ∈
          curvatureMinusOneMetrics R hreg hcurv := by
    obtain ⟨_, _, _, _, _, hrestriction, _⟩ :=
      exists_original_curvature_slice_scaleTwo_equiv R hreg hcurv hcov
    exact hrestriction
  constructor
  · rintro ⟨f, hf, hconf⟩
    obtain ⟨φ, hφ, hscale⟩ := hconf
    let pulled := SmoothSurfaceMetric.pullback f.smooth h.val
    have hpulled : pulled ∈ curvatureMinusOneMetrics R hreg hcurv :=
      haction ⟨f, hf⟩ h.val h.property
    have hidentity : IsRawMetricConformal g.val pulled
        (SmoothSurfaceEquiv.refl R.toRiemannSurface) := by
      refine ⟨φ, hφ, ?_⟩
      intro x a b
      rw [surfaceDifferential_refl_apply, surfaceDifferential_refl_apply]
      exact hscale x a b
    obtain ⟨m, _, hunique⟩ := hnorm X R hreg hcurv genus hgenus hg g.val
    have hg_eq : g.val = m :=
      hunique g.val ⟨g.property, IsRawMetricConformal.refl g.val⟩
    have hp_eq : pulled = m := hunique pulled ⟨hpulled, hidentity⟩
    exact ⟨⟨f, hf⟩, hp_eq.trans hg_eq.symm⟩
  · rintro ⟨f, hpull⟩
    refine ⟨f.val, f.property, ?_⟩
    refine ⟨fun _ => 0, contMDiff_const, ?_⟩
    intro x a b
    change (SmoothSurfaceMetric.pullback f.val.smooth h.val).inner x a b =
      Real.exp (0 : ℝ) * g.val.inner x a b
    rw [Real.exp_zero, one_mul, hpull]

/-- The literal curvature-minus-one pullback orbit quotient is equivalent to
the original Teichmuller space, with its already accepted metric-class map. -/
theorem exists_original_curvatureMinusOne_orbit_equiv
    (hreg : Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (hcurv : Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature.{u})
    (hcov : Unproved.Teichmuller.OriginalMetricGaussianCurvatureCovariance.{u})
    (hnorm : Unproved.Teichmuller.OriginalHyperbolicMetricConformalNormalization.{u})
    {genus : ℕ} (hgenus : R.HasGenus genus) (hg : 1 < genus) :
    let S : Type u := ↥(curvatureMinusOneMetrics R hreg hcurv)
    ∃ O : Setoid S,
      (∀ g h : S,
        O.r g h ↔ ∃ f : OrientedSurfaceAut.homotopyIdentitySubgroup R,
          SmoothSurfaceMetric.pullback f.val.smooth h.val = g.val) ∧
      ∃ E : TeichmullerSpace.{u, v} R ≃ Quotient O,
        ∀ g : S,
          TeichmullerSpace.equivRawMetricStrongQuotient_of_regularity R hreg
              (E.symm (Quotient.mk O g)) =
            RawMetricStrongQuotient.mk g.val := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let S : Type u := ↥(curvatureMinusOneMetrics R hreg hcurv)
  let orbit : S → S → Prop := fun g h =>
    ∃ f : OrientedSurfaceAut.homotopyIdentitySubgroup R,
      SmoothSurfaceMetric.pullback f.val.smooth h.val = g.val
  have horbit (g h : S) : RawMetricStronglyEquivalent R g.val h.val ↔ orbit g h :=
    curvatureMinusOne_strong_iff_pullback_orbit R hreg hcurv hcov hnorm hgenus hg g h
  let O : Setoid S :=
    { r := orbit
      iseqv := ⟨fun g => (horbit g g).mp (RawMetricStronglyEquivalent.refl R g.val),
        fun {g h} hgh => (horbit h g).mp
          (RawMetricStronglyEquivalent.symm R ((horbit g h).mpr hgh)),
        fun {g h k} hgh hhk => (horbit g k).mp
          (RawMetricStronglyEquivalent.trans R
            ((horbit g h).mpr hgh) ((horbit h k).mpr hhk))⟩ }
  let inclusion : Quotient O → RawMetricStrongQuotient R :=
    Quotient.lift (fun g : S => RawMetricStrongQuotient.mk g.val) (by
      intro g h hgh
      exact (RawMetricStrongQuotient.mk_eq_mk_iff g.val h.val).mpr
        ((horbit g h).mpr hgh))
  have hinj : Function.Injective inclusion := by
    intro q q' heq
    revert heq
    refine Quotient.inductionOn₂ q q' ?_
    intro g h heq
    apply Quotient.sound
    exact (horbit g h).mp
      ((RawMetricStrongQuotient.mk_eq_mk_iff g.val h.val).mp heq)
  have hsurj : Function.Surjective inclusion := by
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    obtain ⟨h, hh, _⟩ := hnorm X R hreg hcurv genus hgenus hg g
    let s : S := ⟨h, hh.1⟩
    refine ⟨Quotient.mk O s, ?_⟩
    apply (RawMetricStrongQuotient.mk_eq_mk_iff h g).mpr
    apply RawMetricStronglyEquivalent.symm R
    refine ⟨1, (OrientedSurfaceAut.homotopyIdentitySubgroup R).one_mem, ?_⟩
    exact hh.2
  let I : Quotient O ≃ RawMetricStrongQuotient R := Equiv.ofBijective inclusion ⟨hinj, hsurj⟩
  let T : TeichmullerSpace.{u, v} R ≃ RawMetricStrongQuotient R :=
    TeichmullerSpace.equivRawMetricStrongQuotient_of_regularity R hreg
  let E : TeichmullerSpace.{u, v} R ≃ Quotient O := T.trans I.symm
  refine ⟨O, ?_, E, ?_⟩
  · intro g h
    rfl
  · intro g
    change T (T.symm (I (Quotient.mk O g))) = RawMetricStrongQuotient.mk g.val
    exact T.apply_symm_apply (I (Quotient.mk O g))

end LowDimensionalTopology.Geometry.Teichmuller
