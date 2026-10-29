module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeodesicTwistCollarMetric
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCollarBand
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalCylinderCoordinates
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ModelCoordinates

/-!
# A small intrinsic twist annulus and its chosen lift

The original single-traversal geodesic supplies its full-period matrix and
canonical covering fibers. The same positive normalizer and a strict angular
substrip then give a circle-product tube and its actual connected lifted
component, conditional on the intrinsic distance law for this normalizer.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
open Surfaces Hyperbolic
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private theorem smallTwist_smul_eq_of_projective_eq {B C : Deck}
    (hBC : realSLMobius B = realSLMobius C) (z : ℍ) : B • z = C • z :=
  congrArg (fun f : ℍ ≃ᵢ ℍ => f z)
    (Fuchsian.hSLIsometry_eq_of_realSLMobius_eq B C hBC)

private theorem smallTwist_strip_eq_logarithmic (θ : Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    hypercyclicStrip (θ : ℝ) = Fuchsian.logarithmicCanonicalStrip (Real.tan (θ : ℝ)) := by
  ext z
  have hi := verticalInclination_mem_Ico 0 z
  have himem : verticalInclination 0 z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos, hi.1], hi.2⟩
  have hθmem : (θ : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos, θ.property.1], θ.property.2⟩
  calc
    z ∈ hypercyclicStrip (θ : ℝ) ↔ verticalInclination 0 z < (θ : ℝ) := by
      change |Complex.arg (z : ℂ) - Real.pi / 2| < (θ : ℝ) ↔ _
      rw [verticalInclination_zero_eq_arg]
    _ ↔ Real.tan (verticalInclination 0 z) < Real.tan (θ : ℝ) :=
      (Real.strictMonoOn_tan.lt_iff_lt himem hθmem).symm
    _ ↔ |z.re| / z.im < Real.tan (θ : ℝ) := by
      rw [← verticalLine_pointDist_sinh_inclination, verticalLine_pointDist_sinh, sub_zero]
    _ ↔ z ∈ Fuchsian.logarithmicCanonicalStrip (Real.tan (θ : ℝ)) := by
      change _ ↔ -Real.tan (θ : ℝ) < z.re / z.im ∧ z.re / z.im < Real.tan (θ : ℝ)
      rw [← abs_lt, abs_div, abs_of_pos z.im_pos]

private theorem smallTwist_logDilation_mem_strip
    (θ : ℝ) (t : ℝ) (z : ℍ) :
    Fuchsian.hLogDilationSL t • z ∈ hypercyclicStrip θ ↔ z ∈ hypercyclicStrip θ := by
  change |Complex.arg ((Fuchsian.hLogDilationSL t • z : ℍ) : ℂ) - Real.pi / 2| < θ ↔
    |Complex.arg (z : ℂ) - Real.pi / 2| < θ
  rw [Fuchsian.hLogDilationSL_coe, Complex.arg_real_mul _ (Real.exp_pos _)]

/-- One full-period normalizer gives a small intrinsic annulus and exactly
the connected lifted component through its normalized axis. -/
theorem originalGeodesic_exists_small_intrinsic_twist_collar
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    (q : OriginalClosedGeodesic M)
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s) (_hAΓ : A ∈ Γ)
      (_hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop)
      (_hQA : realSLMobius (Q * A * Q⁻¹) =
        realSLMobius (Fuchsian.hLogDilationSL s)),
      let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
      let θ := canonicalBandWidth s hs
      ∀ _hDistance : Unproved.Teichmuller.OriginalGeodesicIntrinsicLiftDistance q Q,
        ∃ a : ℝ, 0 < a ∧ hypercyclicWidthAngle a = (θ : ℝ) ∧
          q.tubularNeighborhood a = pQ '' hypercyclicStrip (θ : ℝ) ∧
          hypercyclicStrip (θ : ℝ) =
            connectedComponentIn (pQ ⁻¹' q.tubularNeighborhood a) UpperHalfPlane.I ∧
          Nonempty (q.tubularNeighborhood a ≃ₜ
            AddCircle (2 * s) × Set.Ioo (-Real.tan (θ : ℝ)) (Real.tan (θ : ℝ))) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨A, _hA, _ht, hAΓ, hcov, hsimple, hfib⟩ :=
    q.exists_canonical_collar_fibers_of_circle_injective hp hcircle
  obtain ⟨Q, s, hs, hQA⟩ :=
    Fuchsian.realSLMobius_hyperbolic_positive_log_normal_form A hsimple.2.1
  refine ⟨A, Q, s, hs, hAΓ, hcov, hQA, ?_⟩
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  let hpQ : LiZhongQC.IsUniformization ΓQ pQ :=
    LiZhongQC.adjustProjection_isUniformization hp Q
  let θ := canonicalBandWidth s hs
  let S := hypercyclicStrip (θ : ℝ)
  let C := Q * A * Q⁻¹
  have hCΓ : C ∈ ΓQ := Subgroup.mem_map.mpr ⟨A, hAΓ, rfl⟩
  have hCpowers (n : ℤ) : C ^ n = Q * A ^ n * Q⁻¹ := by
    simpa only [C, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      (((MulAut.conj Q).toMonoidHom).map_zpow A n).symm
  have hCaction (n : ℤ) (z : ℍ) :
      C ^ n • z = Fuchsian.hLogDilationSL ((n : ℝ) * s) • z := by
    apply smallTwist_smul_eq_of_projective_eq
    rw [map_zpow, hQA, ← map_zpow, Fuchsian.hLogDilationSL_zpow]
  have hCmem (n : ℤ) (z : ℍ) : C ^ n • z ∈ S ↔ z ∈ S := by
    rw [hCaction]
    exact smallTwist_logDilation_mem_strip (θ : ℝ) _ z
  have hcan (z : ℍ) (hz : z ∈ S) : Q⁻¹ • z ∈ hCanonicalRegion A := by
    have hband : z ∈ closedAngularBand θ :=
      (mem_closedAngularBand_iff θ z).mpr (le_of_lt hz)
    have hD := closedAngularBand_canonicalBandWidth_subset_hCanonicalRegion s hs hband
    rw [← hCanonicalRegion_congr _ _ hQA] at hD
    apply (hCanonicalRegion_conjugation_mem A Q (Q⁻¹ • z)).mp
    simpa only [smul_inv_smul] using hD
  have hfibQ (z : ℍ) (hz : z ∈ S) (w : ℍ) (hw : w ∈ S) :
      pQ z = pQ w ↔ ∃ n : ℤ, w = C ^ n • z := by
    constructor
    · intro hzw
      obtain ⟨n, hn⟩ := (hfib (Q⁻¹ • z) (hcan z hz) (Q⁻¹ • w) (hcan w hw)).mp hzw
      refine ⟨n, ?_⟩
      calc
        w = Q • (Q⁻¹ • w) := (smul_inv_smul Q w).symm
        _ = Q • (A ^ n • (Q⁻¹ • z)) := by rw [hn]
        _ = C ^ n • z := by rw [hCpowers, mul_smul, mul_smul]
    · rintro ⟨n, rfl⟩
      exact (LiZhongQC.s30a_p_smul hpQ (ΓQ.zpow_mem hCΓ n) z).symm
  have hSlog : S = Fuchsian.logarithmicCanonicalStrip (Real.tan (θ : ℝ)) :=
    smallTwist_strip_eq_logarithmic θ
  have hSo : IsOpen S := by
    rw [hSlog]
    exact isOpen_Ioo.preimage
      (UpperHalfPlane.continuous_re.div UpperHalfPlane.continuous_im (fun z => z.im_pos.ne'))
  have hI : UpperHalfPlane.I ∈ S := by
    change |Complex.arg (UpperHalfPlane.I : ℂ) - Real.pi / 2| < (θ : ℝ)
    simpa only [UpperHalfPlane.coe_I, Complex.arg_I, sub_self, abs_zero] using θ.property.1
  have hpre : IsPreconnected S :=
    (hypercyclicStrip_hConvex (θ : ℝ) θ.property.1 θ.property.2).isPreconnected
  have hstable (δ : Deck) (hδ : δ ∈ ΓQ)
      (hoverlap : (((fun z : ℍ => δ • z) '' S) ∩ S).Nonempty) :
      (fun z : ℍ => δ • z) '' S = S := by
    obtain ⟨_, ⟨z, hz, rfl⟩, hw⟩ := hoverlap
    obtain ⟨n, hn⟩ := (hfibQ z hz (δ • z) hw).mp
      (LiZhongQC.s30a_p_smul hpQ hδ z).symm
    let B := (C ^ n)⁻¹ * δ
    have hBΓ : B ∈ ΓQ := ΓQ.mul_mem (ΓQ.inv_mem (ΓQ.zpow_mem hCΓ n)) hδ
    have hBfix : B • z = z := by
      dsimp only [B]
      rw [mul_smul, hn, inv_smul_smul]
    have hBproj : realSLMobius B = 1 := by
      rcases LiZhongQC.s27g_actsFreely hpQ B hBΓ z hBfix with hB | hB
      · rw [hB, map_one]
      · rw [hB, realSLMobius_neg, map_one]
    have hδproj : realSLMobius (C ^ n) = realSLMobius δ :=
      inv_mul_eq_one.mp (by simpa only [B, map_mul, map_inv] using hBproj)
    have hδaction (x : ℍ) : δ • x = C ^ n • x :=
      smallTwist_smul_eq_of_projective_eq hδproj.symm x
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change δ • y ∈ S
      rw [hδaction]
      exact (hCmem n y).mpr hy
    · intro hx
      refine ⟨C ^ (-n) • x, (hCmem (-n) x).mpr hx, ?_⟩
      change δ • (C ^ (-n) • x) = x
      rw [hδaction, zpow_neg, smul_inv_smul]
  have hcomponent : S = connectedComponentIn (pQ ⁻¹' (pQ '' S)) UpperHalfPlane.I := by
    let V : Set ℍ := ⋃ δ : {δ : ΓQ // (fun z : ℍ => δ.val • z) '' S ≠ S},
      (fun z : ℍ => δ.val.val • z) '' S
    have hVo : IsOpen V := isOpen_iUnion (fun δ =>
      (Homeomorph.smul δ.val.val : ℍ ≃ₜ ℍ).isOpenMap S hSo)
    have hdisj : Disjoint S V := by
      apply Set.disjoint_left.mpr
      intro z hz hzV
      obtain ⟨δ, hδz⟩ := Set.mem_iUnion.mp hzV
      exact δ.property (hstable δ.val.val δ.val.property ⟨z, hδz, hz⟩)
    have hST : S ⊆ pQ ⁻¹' (pQ '' S) := fun z hz => ⟨z, hz, rfl⟩
    have hTV : pQ ⁻¹' (pQ '' S) ⊆ S ∪ V := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hy
      obtain ⟨δ, hδ, hδz⟩ := (hpQ.2.2.2 z y).mp hzy
      by_cases hδS : (fun z : ℍ => δ • z) '' S = S
      · apply Or.inl
        rw [← hδS]
        exact ⟨z, hz, hδz⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨⟨δ, hδ⟩, hδS⟩, z, hz, hδz⟩)
    apply Set.Subset.antisymm (hpre.subset_connectedComponentIn hI hST)
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hSo hVo hdisj
      ((connectedComponentIn_subset _ _).trans hTV)
      ⟨UpperHalfPlane.I, mem_connectedComponentIn (hST hI), hI⟩
  let b := Real.tan (θ : ℝ)
  let E : S ≃ₜ Fuchsian.logarithmicCanonicalStrip b := Homeomorph.setCongr hSlog
  let F : C(S, pQ '' S) :=
    ⟨fun z => ⟨pQ z.val, z.val, z.property, rfl⟩,
      (hpQ.1.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hF : IsOpenQuotientMap F := by
    refine ⟨?_, F.continuous, ?_⟩
    · rintro ⟨_, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · exact (hpQ.1.isLocalHomeomorph.isOpenMap.domRestrict hSo).codRestrict _
  have hCdilation : realSLMobius C = stableAxisDilation (2 * s) :=
    hQA.trans ((Fuchsian.realSLMobius_logDilation s).trans
      (Fuchsian.realSLMobius_verticalDilation (Real.exp (2 * s)) (Real.exp_pos _)))
  let r : Setoid (Fuchsian.logarithmicCanonicalStrip b) :=
    (MulAction.orbitRel (Subgroup.zpowers (stableAxisDilation (2 * s)))
      Mobius.ExtendedComplex).comap (fun z => Mobius.halfPlaneBoundaryPoint z.val)
  have hker (z w : S) : Setoid.ker F z w ↔ r (E z) (E w) := by
    constructor
    · intro hzw
      have hzw' : pQ w.val = pQ z.val := (congrArg Subtype.val hzw).symm
      obtain ⟨n, hn⟩ := (hfibQ w.val w.property z.val z.property).mp hzw'
      refine ⟨⟨stableAxisDilation (2 * s) ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩, ?_⟩
      change (stableAxisDilation (2 * s) ^ n).val (Mobius.halfPlaneBoundaryPoint w.val) =
        Mobius.halfPlaneBoundaryPoint z.val
      rw [← hCdilation, ← map_zpow]
      change (realSLMobius (C ^ n)).val (w.val : ℂ) = (z.val : ℂ)
      rw [realSLMobius_action, ← hn]
    · rintro ⟨δ, hδ⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp δ.property
      have hzw : C ^ n • w.val = z.val := by
        apply Mobius.halfPlaneBoundaryPoint_injective
        change (((C ^ n • w.val : ℍ) : ℂ) : Mobius.ExtendedComplex) = (z.val : ℂ)
        rw [← realSLMobius_action, map_zpow, hCdilation, hn]
        exact hδ
      apply Subtype.ext
      change pQ z.val = pQ w.val
      rw [← hzw, LiZhongQC.s30a_p_smul hpQ (ΓQ.zpow_mem hCΓ n)]
  have Eimage : (pQ '' S) ≃ₜ AddCircle (2 * s) × Set.Ioo (-b) b :=
    hF.isQuotientMap.homeomorph.symm.trans
      ((Homeomorph.Quotient.congr (rY := r) E hker).trans
        (Fuchsian.logarithmicCanonicalStripQuotientHomeomorph (2 * s) b))
  dsimp only
  intro hDistance
  obtain ⟨a, ha, hwidth⟩ := exists_hypercyclic_width θ.property.1 θ.property.2
  have hImage : q.tubularNeighborhood a = pQ '' S := by
    rw [givenOriginalGeodesic_metricTube_eq_normalizedAngularImage R q hp A Q s hs
      hAΓ hcov hQA hDistance a ha, hwidth]
  refine ⟨a, ha, hwidth, hImage, ?_, ?_⟩
  · rw [hImage]
    exact hcomponent
  · rw [hImage]
    exact ⟨Eimage⟩

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
