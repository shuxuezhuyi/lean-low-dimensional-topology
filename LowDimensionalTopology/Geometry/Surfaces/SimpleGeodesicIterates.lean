module

public import LowDimensionalTopology.Geometry.Surfaces.SimpleWolpertImage
public import Mathlib.Logic.Function.Iterate

/-!
# Simple geodesic representatives along an actual homeomorphism orbit

Each representative retains the full free class of its corresponding iterated
circle. Successive simple representatives satisfy Wolpert's bound with the same supplied
quasiconformal constant, so their complete period lengths have the usual
geometric growth bound.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Teichmuller

/-- The actual orbit of an essential circle has simple geodesic representatives
whose whole-period lengths grow by at most the original supplied QC constant. -/
theorem EssentialSimpleCircle.exists_simple_wolpert_iterates
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (hSimple : LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives R g M)
    (c : EssentialSimpleCircle X) (q : OriginalClosedGeodesic M)
    (hq : LiZhongQC.FreelyHomotopic (circleRepresentativeLoop c.val) q.toLoop)
    (f : X ≃ₜ X) {K : ℝ}
    (hf : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsKQCRS f K) :
    ∃ qs : ℕ → OriginalClosedGeodesic M,
      (qs 0).lengthTrace = q.lengthTrace ∧ ∀ n : ℕ,
        LiZhongQC.FreelyHomotopic
            (circleRepresentativeLoop (((EssentialSimpleCircle.mapHomeomorph f)^[n]) c).val)
            (qs n).toLoop ∧
          Function.Injective ((qs n).periodic.lift : AddCircle (1 : ℝ) → X) ∧
            (qs n).length.toReal ≤ K ^ n * q.length.toReal := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  let cs : ℕ → EssentialSimpleCircle X :=
    fun n => ((EssentialSimpleCircle.mapHomeomorph f)^[n]) c
  choose qs hqs hqi using fun n : ℕ => hSimple hg hgenus (cs n)
  have hzeroTrace : (qs 0).lengthTrace = q.lengthTrace :=
    (qs 0).lengthTrace_eq_of_freelyHomotopic q
      (LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm (hqs 0)) hq)
  have hzeroLength : (qs 0).length = q.length := congrArg Prod.snd hzeroTrace
  have hstep (n : ℕ) : (qs (n + 1)).length.toReal ≤ K * (qs n).length.toReal := by
    obtain ⟨r, hr, _hri, hupper⟩ :=
      EssentialSimpleCircle.exists_simple_wolpert_image
        R hg hgenus M hSimple (cs n) (qs n) (hqs n) f hf
    have hr' : LiZhongQC.FreelyHomotopic
        (circleRepresentativeLoop (cs (n + 1)).val) r.toLoop := by
      simpa only [cs, Function.iterate_succ_apply'] using hr
    have hlength : (qs (n + 1)).length = r.length :=
      congrArg Prod.snd ((qs (n + 1)).lengthTrace_eq_of_freelyHomotopic r
        (LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm (hqs (n + 1))) hr'))
    rw [hlength]
    exact hupper
  have hbound (n : ℕ) : (qs n).length.toReal ≤ K ^ n * q.length.toReal := by
    induction n with
    | zero =>
        simpa only [pow_zero, one_mul, hzeroLength] using
          (le_rfl : q.length.toReal ≤ q.length.toReal)
    | succ n ih =>
        calc
          (qs (n + 1)).length.toReal ≤ K * (qs n).length.toReal := hstep n
          _ ≤ K * (K ^ n * q.length.toReal) :=
            mul_le_mul_of_nonneg_left ih (zero_le_one.trans hf.1)
          _ = K ^ (n + 1) * q.length.toReal := by rw [pow_succ]; ring
  exact ⟨qs, hzeroTrace, fun n => ⟨hqs n, hqi n, hbound n⟩⟩

end LowDimensionalTopology.Geometry.Surfaces
