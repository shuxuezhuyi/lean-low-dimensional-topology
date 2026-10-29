module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalReflectedClosedSurface
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# The same original uniformization on the lower half-plane

The covering is reflected by literal conjugation of its argument. Its fibres
are the orbits of the same real matrices, embedded in the complex matrix
group. This identifies the conjugate atlas with the lower-half-plane model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

/-- The actual lower half-plane, with its original open-subspace topology. -/
def originalMirrorLowerDomain : TopologicalSpace.Opens ℂ :=
  ⟨LiZhongQC.lowerHalf, LiZhongQC.isOpen_lowerHalf⟩

/-- Conjugation is a homeomorphism from the lower half-plane to the upper one. -/
def originalMirrorLowerConjugation : originalMirrorLowerDomain ≃ₜ UpperHalfPlane where
  toFun z := ⟨conj (z : ℂ), by
    change 0 < -(z : ℂ).im
    exact neg_pos.mpr z.2⟩
  invFun τ := ⟨conj (τ : ℂ), by
    change -(τ : ℂ).im < 0
    exact neg_neg_of_pos τ.im_pos⟩
  left_inv z := Subtype.ext (Complex.conj_conj (z : ℂ))
  right_inv τ := UpperHalfPlane.ext (Complex.conj_conj (τ : ℂ))
  continuous_toFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    (Complex.continuous_conj.comp continuous_subtype_val)
  continuous_invFun :=
    (Complex.continuous_conj.comp UpperHalfPlane.continuous_coe).subtype_mk
      (fun τ => by
        change -(τ : ℂ).im < 0
        exact neg_neg_of_pos τ.im_pos)

/-- The actual lower conjugation retains its literal point coordinate. -/
@[simp] theorem originalMirrorLowerConjugation_coe (z : originalMirrorLowerDomain) :
    ((originalMirrorLowerConjugation z : UpperHalfPlane) : ℂ) = conj (z : ℂ) := rfl

/-- The reflected covering is fixed off its actual lower-half-plane domain. -/
def originalMirrorCover {S : Type} (p : UpperHalfPlane → S) (z : ℂ) : S := by
  classical
  exact if hz : z ∈ LiZhongQC.lowerHalf then p (originalMirrorLowerConjugation ⟨z, hz⟩)
    else p UpperHalfPlane.I

/-- On the true domain the covering uses exactly the conjugated old argument. -/
theorem originalMirrorCover_apply {S : Type} (p : UpperHalfPlane → S)
    (z : originalMirrorLowerDomain) :
    originalMirrorCover p z = p (originalMirrorLowerConjugation z) := by
  have hz : (z : ℂ) ∈ LiZhongQC.lowerHalf := z.2
  rw [originalMirrorCover, dite_eq_left hz]

/-- The canonical mirror map gives the literal original covering square. -/
theorem originalMirrorCover_square (S : LiZhongQC.ClosedRS.{0})
    (p : UpperHalfPlane → S.carrier) (τ : UpperHalfPlane) :
    originalMirrorCover p (conj (τ : ℂ)) = originalMirrorCanonicalMap S (p τ) := by
  have hτ : conj (τ : ℂ) ∈ LiZhongQC.lowerHalf := by
    change -(τ : ℂ).im < 0
    exact neg_neg_of_pos τ.im_pos
  rw [originalMirrorCover, dite_eq_left hτ]
  change p (originalMirrorLowerConjugation ⟨conj (τ : ℂ), hτ⟩) = p τ
  apply congrArg p
  exact UpperHalfPlane.ext (Complex.conj_conj (τ : ℂ))

/-- The actual old holomorphic covering becomes holomorphic in the mirror atlas. -/
theorem originalMirrorCover_mdifferentiable (S : LiZhongQC.ClosedRS.{0})
    (p : UpperHalfPlane → S.carrier)
    (hp : letI := S.chartedSpace
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) :
    letI := originalMirrorChartedSpace S
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : originalMirrorLowerDomain => originalMirrorCover p z) := by
  have hcoord (z : originalMirrorLowerDomain) : DifferentiableAt ℂ
      (fun w => S.chartedSpace.chartAt (originalMirrorCover p z)
        (p (UpperHalfPlane.ofComplex w))) (conj (z : ℂ)) := by
    have hsource : p (originalMirrorLowerConjugation z) ∈
        (S.chartedSpace.chartAt (originalMirrorCover p z)).source := by
      rw [← originalMirrorCover_apply p z]
      exact mem_chart_source ℂ _
    have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (fun τ : UpperHalfPlane =>
          S.chartedSpace.chartAt (originalMirrorCover p z) (p τ))
        (originalMirrorLowerConjugation z) :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ _) hsource).comp
        (originalMirrorLowerConjugation z) (hp (originalMirrorLowerConjugation z))
    simpa only [Function.comp_def, originalMirrorLowerConjugation_coe] using
      UpperHalfPlane.mdifferentiableAt_iff.mp hm
  have hpg : (fun z : originalMirrorLowerDomain => originalMirrorCover p z) =
      p ∘ originalMirrorLowerConjugation := by
    funext z
    exact originalMirrorCover_apply p z
  have hcont : Continuous (fun z : originalMirrorLowerDomain => originalMirrorCover p z) := by
    rw [hpg]
    exact hp.continuous.comp originalMirrorLowerConjugation.continuous
  let := originalMirrorChartedSpace S
  let := originalMirror_isManifold S
  intro z
  apply mdifferentiableAt_iff_target.mpr
  refine ⟨hcont.continuousAt, ?_⟩
  have hd : DifferentiableAt ℂ
      (fun w => conj (S.chartedSpace.chartAt (originalMirrorCover p z)
        (p (UpperHalfPlane.ofComplex (conj w))))) (z : ℂ) := by
    simpa only [Function.comp_def, Complex.conj_conj] using (hcoord z).conj_conj
  have hm := hd.mdifferentiableAt.comp z
    ((contMDiff_subtype_val (n := ω)).mdifferentiable (by simp) z)
  have hfun : (extChartAt 𝓘(ℂ) (originalMirrorCover p z) ∘
      (fun w : originalMirrorLowerDomain => originalMirrorCover p w)) =
      fun w : originalMirrorLowerDomain =>
        conj (S.chartedSpace.chartAt (originalMirrorCover p z)
          (p (UpperHalfPlane.ofComplex (conj (w : ℂ))))) := by
    funext w
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe,
      modelWithCornersSelf_coe, Function.comp_apply]
    change conj (S.chartedSpace.chartAt (originalMirrorCover p z)
        (originalMirrorCover p w)) =
      conj (S.chartedSpace.chartAt (originalMirrorCover p z)
        (p (UpperHalfPlane.ofComplex (conj (w : ℂ)))))
    have hwpos : 0 < (conj (w : ℂ)).im := by
      change 0 < -(w : ℂ).im
      exact neg_pos.mpr w.2
    have harg : UpperHalfPlane.ofComplex (conj (w : ℂ)) =
        originalMirrorLowerConjugation w := by
      apply UpperHalfPlane.ext
      rw [originalMirrorLowerConjugation_coe]
      exact congrArg (fun τ : UpperHalfPlane => (τ : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos hwpos)
    rw [originalMirrorCover_apply p w, harg]
  rw [hfun]
  exact hm

/-- The lower-plane model uses precisely the same original real group. -/
theorem originalMirrorCover_isKleinUniformization (S : LiZhongQC.ClosedRS.{0})
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → S.carrier)
    (hp : @LiZhongQC.IsUniformization S.carrier S.topologicalSpace S.chartedSpace Γ p) :
    @LiZhongQC.IsKleinUniformization S.carrier S.topologicalSpace
      (originalMirrorChartedSpace S)
      (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))
      originalMirrorLowerDomain (originalMirrorCover p) := by
  have hpg : (fun z : originalMirrorLowerDomain => originalMirrorCover p z) =
      p ∘ originalMirrorLowerConjugation := by
    funext z
    exact originalMirrorCover_apply p z
  refine ⟨?_, originalMirrorCover_mdifferentiable S p hp.2.1, ?_, ?_⟩
  · rw [hpg]
    exact hp.1.comp_homeomorph originalMirrorLowerConjugation
  · apply eq_univ_iff_forall.mpr
    intro s
    obtain ⟨τ, hτ⟩ := hp.2.2.1 s
    refine ⟨conj (τ : ℂ), ?_, ?_⟩
    · change -(τ : ℂ).im < 0
      exact neg_neg_of_pos τ.im_pos
    · exact (originalMirrorCover_square S p τ).trans hτ
  · intro z hz w hw
    let z' : originalMirrorLowerDomain := ⟨z, hz⟩
    let w' : originalMirrorLowerDomain := ⟨w, hw⟩
    rw [show originalMirrorCover p z = p (originalMirrorLowerConjugation z') from
      originalMirrorCover_apply p z',
      show originalMirrorCover p w = p (originalMirrorLowerConjugation w') from
        originalMirrorCover_apply p w']
    rw [hp.2.2.2]
    constructor
    · rintro ⟨γ, hγ, hzw⟩
      refine ⟨Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ,
        Subgroup.mem_map_of_mem _ hγ, ?_, ?_⟩
      · change (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0
        intro hden
        apply LiZhongQC.h23l_b_den_ne γ (z := conj z)
          (by change 0 < -z.im; exact neg_pos.mpr hz)
        simpa only [map_add, map_mul, Complex.conj_ofReal, map_zero] using congrArg conj hden
      · change w = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)
        have hval := congrArg (fun τ : UpperHalfPlane => (τ : ℂ)) hzw
        rw [LiZhongQC.h23l_b_coe_smul] at hval
        simpa only [originalMirrorLowerConjugation_coe, map_div₀, map_add, map_mul,
          Complex.conj_ofReal, Complex.conj_conj] using (congrArg conj hval).symm
    · rintro ⟨δ, hδ, _hden, hwz⟩
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hδ
      change w = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) at hwz
      refine ⟨γ, hγ, ?_⟩
      apply UpperHalfPlane.ext
      rw [LiZhongQC.h23l_b_coe_smul]
      simpa only [originalMirrorLowerConjugation_coe, map_div₀, map_add, map_mul,
        Complex.conj_ofReal] using (congrArg conj hwz).symm

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
