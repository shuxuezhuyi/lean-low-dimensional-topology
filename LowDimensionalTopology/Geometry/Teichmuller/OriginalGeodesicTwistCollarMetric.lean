module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalGeodesicIntrinsicLiftDistance
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HypercycleDistance
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalSimpleClosedGeodesic
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedLengthSpectrum
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.PureHyperbolicSharpness

/-!
# The actual intrinsic twist tube is the image of its open angular strip

The original distance to the entire geodesic trace is compared with all trace
lifts. The same full-period axis, normalizer and covering fiber law then turn
that strict distance sublevel into the projected open angular strip. The
statement does not assert that a tube of an arbitrary radius is embedded.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
open Surfaces Hyperbolic
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The given original intrinsic radial tube equals the image of the same
normalized open strip, using the complete trace preimage in the distance law. -/
theorem givenOriginalGeodesic_metricTube_eq_normalizedAngularImage
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    (q : OriginalClosedGeodesic M)
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (A Q : Deck) (s : ℝ) (hs : 0 < s)
    (hAΓ : A ∈ Γ)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop)
    (hQA : realSLMobius (Q * A * Q⁻¹) = realSLMobius (Fuchsian.hLogDilationSL s))
    (hDistance : Unproved.Teichmuller.OriginalGeodesicIntrinsicLiftDistance q Q) :
    ∀ a : ℝ, 0 < a →
      q.tubularNeighborhood a =
        LiZhongQC.adjustProjection M.halfPlaneCover Q ''
          hypercyclicStrip (hypercyclicWidthAngle a) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
    LiZhongQC.adjustProjection_isUniformization hp Q
  have hNoCentral (hcentral : A = 1 ∨ A = -1) : False := by
    have hzero := LiZhongQC.s30a_len_zero hp hAΓ
      (hcentral.elim Or.inl (fun h => Or.inr (Or.inl h))) hcov
    exact (ne_of_gt q.length_pos_and_ne_top.1) (q.length_eq_freeHomotopyLength.trans hzero)
  have hhyper : LiZhongQC.IsHyperbolic A := LiZhongQC.s27f_hyp hp hAΓ
    (fun h => hNoCentral (Or.inl h)) (fun h => hNoCentral (Or.inr h))
  have habs : 2 < |Matrix.trace A.val| := by
    simpa only [LiZhongQC.IsHyperbolic, LiZhongQC.slTrace, Matrix.trace_fin_two] using hhyper
  have ht : 4 < (Matrix.trace A.val) ^ 2 := by
    nlinarith [sq_abs (Matrix.trace A.val)]
  have hA := Fuchsian.realSLMobius_ne_one_of_trace_sq_gt_four A ht
  let C := Q * A * Q⁻¹
  let D := Fuchsian.hLogDilationSL s
  have hC : realSLMobius C ≠ 1 := hSL_nontrivial_conjugation A Q hA
  have htC : 4 < (Matrix.trace C.val) ^ 2 := by
    dsimp only [C]
    rwa [hSL_trace_conjugation]
  have hHC := (realSLMobius_hyperbolic_iff C hC).mpr htC
  have hHD : Mobius.MobiusHyperbolic (realSLMobius D) := hQA ▸ hHC
  have hD : realSLMobius D ≠ 1 := hHD.1.1
  have htD := (realSLMobius_hyperbolic_iff D hD).mp hHD
  have hCD := Fuchsian.hHyperbolicAxis_eq_of_realSLMobius_eq C D hC hD htC htD hQA
  have hImage : (fun z : ℍ => Q • z) '' (hHyperbolicAxis A hA ht).carrier =
      (HalfPlaneLine.vertical 0).carrier := by
    rw [← Fuchsian.hLogDilationSL_hyperbolic_axis s hs hD htD, ← hCD,
      hHyperbolicAxis_conjugation A Q hA ht, HalfPlaneLine.realGLMap_carrier]
    rfl
  have hproject : pQ ∘ (fun z : ℍ => Q • z) = M.halfPlaneCover := by
    funext z
    change M.halfPlaneCover (Q⁻¹ • (Q • z)) = M.halfPlaneCover z
    rw [inv_smul_smul]
  have htrace : Set.range q.curve = pQ '' (HalfPlaneLine.vertical 0).carrier := by
    calc
      Set.range q.curve = M.halfPlaneCover '' (hHyperbolicAxis A hA ht).carrier :=
        q.trace_eq_axis_image_of_covers hp A hAΓ hA ht hcov
      _ = pQ '' ((fun z : ℍ => Q • z) '' (hHyperbolicAxis A hA ht).carrier) := by
        rw [Set.image_image]
        exact congrArg (fun f : ℍ → X => f '' (hHyperbolicAxis A hA ht).carrier) hproject.symm
      _ = pQ '' (HalfPlaneLine.vertical 0).carrier := by rw [hImage]
  intro a ha
  ext x
  constructor
  · intro hx
    change q.distanceToTrace x < ENNReal.ofReal a at hx
    obtain ⟨z, hz⟩ := hpQ.2.2.1 x
    have hnear :
        (⨅ w : {w : ℍ // pQ w ∈ Set.range q.curve}, ENNReal.ofReal (dist z w.val)) <
          ENNReal.ofReal a := by
      rw [← hDistance z]
      change q.distanceToTrace (pQ z) < ENNReal.ofReal a
      rw [hz]
      exact hx
    obtain ⟨w, hw⟩ := iInf_lt_iff.mp hnear
    have hw' : dist z w.val < a := (ENNReal.ofReal_lt_ofReal_iff ha).mp hw
    have hwtrace : pQ w.val ∈ pQ '' (HalfPlaneLine.vertical 0).carrier := by
      rw [← htrace]
      exact w.property
    obtain ⟨v, hv, hvw⟩ := hwtrace
    obtain ⟨δ, hδ, hδv⟩ := (hpQ.2.2.2 v w.val).mp hvw
    have hdist : dist (δ⁻¹ • z) v = dist z w.val := by
      calc
        dist (δ⁻¹ • z) v = dist (δ⁻¹ • z) (δ⁻¹ • w.val) := by
          rw [← hδv, inv_smul_smul]
        _ = dist z w.val := (isometry_smul ℍ δ⁻¹).dist_eq _ _
    have hpoint : (HalfPlaneLine.vertical 0).pointDist (δ⁻¹ • z) < a := by
      calc
        (HalfPlaneLine.vertical 0).pointDist (δ⁻¹ • z) ≤ dist (δ⁻¹ • z) v :=
          Metric.infDist_le_dist_of_mem hv
        _ = dist z w.val := hdist
        _ < a := hw'
    refine ⟨δ⁻¹ • z, (verticalLine_distance_lt_iff_strip a ha _).mp hpoint, ?_⟩
    exact (LiZhongQC.s30a_p_smul hpQ (ΓQ.inv_mem hδ) z).trans hz
  · rintro ⟨z, hz, rfl⟩
    change q.distanceToTrace (pQ z) < ENNReal.ofReal a
    rw [hDistance z]
    let foot := (HalfPlaneLine.vertical 0).orthogonalFoot z
    have hfoot : foot ∈ (HalfPlaneLine.vertical 0).carrier :=
      (HalfPlaneLine.vertical 0).orthogonalFoot_mem z
    let w : {w : ℍ // pQ w ∈ Set.range q.curve} :=
      ⟨foot, by rw [htrace]; exact ⟨foot, hfoot, rfl⟩⟩
    have hdist : dist z foot < a := by
      rw [← (HalfPlaneLine.vertical 0).pointDist_eq_orthogonalFoot z]
      exact (verticalLine_distance_lt_iff_strip a ha z).mpr hz
    exact (iInf_le _ w).trans_lt ((ENNReal.ofReal_lt_ofReal_iff ha).mpr hdist)

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
