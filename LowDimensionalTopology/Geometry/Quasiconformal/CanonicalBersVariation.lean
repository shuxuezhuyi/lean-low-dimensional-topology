/-
The normalized-solution and conformal-inverse APIs are from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2,
under Apache 2.0. The actual planar inverse is retained throughout.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.SchwarzianIdentityVariation

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation

/-- The actual normalized solution for the original chosen coefficient. -/
def baseMap (μ : LiZhongQC.BeltramiH) : ℂ → ℂ :=
  LiZhongQC.normalizedSolution μ.val

/-- The actual global planar inverse of the normalized solution. -/
def baseInverse (μ : LiZhongQC.BeltramiH) : ℂ → ℂ :=
  Function.invFunOn (baseMap μ) univ

/-- The actual lower-half-plane image, with no fixed-half-plane identification. -/
def lowerImage (μ : LiZhongQC.BeltramiH) : Set ℂ :=
  baseMap μ '' LiZhongQC.lowerHalf

/-- The actual normalized solution is globally injective. -/
theorem baseMap_injective (μ : LiZhongQC.BeltramiH) : Function.Injective (baseMap μ) := by
  obtain ⟨K, hK⟩ := (LiZhongQC.ut_spec μ).1
  exact Set.injOn_univ.mp hK.2.2.1.2.1

/-- The global inverse is a left inverse on the entire plane. -/
theorem baseMap_leftInverse (μ : LiZhongQC.BeltramiH) :
    Function.LeftInverse (baseInverse μ) (baseMap μ) := by
  intro z
  have hi : InjOn (baseMap μ) univ := fun _ _ _ _ h => baseMap_injective μ h
  exact hi.leftInvOn_invFunOn (mem_univ z)

/-- The global inverse is a right inverse on the entire plane. -/
theorem baseMap_rightInverse (μ : LiZhongQC.BeltramiH) :
    Function.RightInverse (baseInverse μ) (baseMap μ) := by
  intro z
  apply Function.invFunOn_eq
  change z ∈ LiZhongQC.normalizedSolution μ.val '' univ
  rw [(LiZhongQC.ut_spec μ).2.1]
  exact mem_univ z

/-- Conformality makes the actual lower image open. -/
theorem lowerImage_isOpen (μ : LiZhongQC.BeltramiH) : IsOpen (lowerImage μ) :=
  (LiZhongQC.ut_conformal_lowerHalf μ).isOpen LiZhongQC.isOpen_lowerHalf

/-- On the actual lower image the global inverse equals the restricted inverse. -/
theorem baseInverse_eq_restricted (μ : LiZhongQC.BeltramiH) {z : ℂ}
    (hz : z ∈ lowerImage μ) :
    baseInverse μ z = Function.invFunOn (baseMap μ) LiZhongQC.lowerHalf z := by
  apply baseMap_injective μ
  exact (baseMap_rightInverse μ z).trans (Function.invFunOn_eq hz).symm

/-- The actual global inverse carries the actual lower image into the lower half-plane. -/
theorem baseInverse_mapsTo_lowerHalf (μ : LiZhongQC.BeltramiH) :
    MapsTo (baseInverse μ) (lowerImage μ) LiZhongQC.lowerHalf := by
  intro z hz
  rw [baseInverse_eq_restricted μ hz]
  exact Function.invFunOn_mem hz

/-- The same actual global inverse is holomorphic on its actual lower image. -/
theorem baseInverse_differentiableOn (μ : LiZhongQC.BeltramiH) :
    DifferentiableOn ℂ (baseInverse μ) (lowerImage μ) := by
  have hi := (LiZhongQC.ut_conformal_lowerHalf μ).symm LiZhongQC.isOpen_lowerHalf
  exact hi.1.congr fun z hz => baseInverse_eq_restricted μ hz


/-- The genuine normalized quotient family uses the same fixed GLOBAL inverse.
Its spatial domain will be the actual lower image of the original base map. -/
def quotientFamily (σ : ℂ → LiZhongQC.BeltramiH) (t w : ℂ) : ℂ :=
  baseMap (σ t) (baseInverse (σ 0) w)

/-- The actual infinitesimal coefficient of that nonsymmetric quotient family. -/
def infinitesimalCoefficient (σ : ℂ → LiZhongQC.BeltramiH) : ℂ → ℂ :=
  LiZhongQC.ahT_dot (fun ζ => deriv (fun t => (σ t).val ζ) 0)
    (σ 0).val (baseMap (σ 0))

/-- The actual quotient at the base parameter is globally the identity. -/
theorem quotientFamily_zero (σ : ℂ → LiZhongQC.BeltramiH) :
    quotientFamily σ 0 = id := by
  funext w
  exact baseMap_rightInverse (σ 0) w

/-- Every map in this actual family is holomorphic on the SAME fixed lower image. -/
theorem quotientFamily_differentiableOn (σ : ℂ → LiZhongQC.BeltramiH) (t : ℂ) :
    DifferentiableOn ℂ (quotientFamily σ t) (lowerImage (σ 0)) :=
  (LiZhongQC.ut_conformal_lowerHalf (σ t)).1.comp
    (baseInverse_differentiableOn (σ 0)) (baseInverse_mapsTo_lowerHalf (σ 0))

/-- The real arbitrary-base Ahlfors variation is evaluated at the original
nonsymmetric normalized map, with its actual quotient coefficient. -/
theorem hasDerivAt_quotientFamily
    {P : Set ℂ} (hP : IsOpen P) (h0 : (0 : ℂ) ∈ P)
    {σ : ℂ → LiZhongQC.BeltramiH} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hkP : ∀ t ∈ P, LiZhongQC.IsBeltramiCoeff (σ t).val univ k)
    (hhol : ∀ ζ, DifferentiableOn ℂ (fun t => (σ t).val ζ) P) (w : ℂ) :
    HasDerivAt (fun t => quotientFamily σ t w)
      (LiZhongQC.ahVar (infinitesimalCoefficient σ) w) 0 := by
  have h := LiZhongQC.ahT_hasDerivAt hP hk0 hk1 hkP hhol
    (fun t _ => LiZhongQC.ut_spec (σ t)) h0 (baseInverse (σ 0) w)
  change HasDerivAt (fun t => quotientFamily σ t w)
    (LiZhongQC.ahVar (infinitesimalCoefficient σ)
      (baseMap (σ 0) (baseInverse (σ 0) w))) 0 at h
  rw [baseMap_rightInverse (σ 0) w] at h
  exact h

/-- Parameter holomorphy here is proved for the actual normalized solutions.
The coefficient representatives must be pointwise holomorphic on the open domain. -/
theorem quotientFamily_parameter_differentiableOn
    {P : Set ℂ} (hP : IsOpen P) {σ : ℂ → LiZhongQC.BeltramiH}
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hkP : ∀ t ∈ P, LiZhongQC.IsBeltramiCoeff (σ t).val univ k)
    (hhol : ∀ ζ, DifferentiableOn ℂ (fun t => (σ t).val ζ) P) (w : ℂ) :
    DifferentiableOn ℂ (fun t => quotientFamily σ t w) P := by
  intro t ht
  exact (LiZhongQC.ahT_hasDerivAt hP hk0 hk1 hkP hhol
    (fun s _ => LiZhongQC.ut_spec (σ s)) ht
    (baseInverse (σ 0) w)).differentiableAt.differentiableWithinAt

/-- The genuine normalized-map bound is transported through the actual fixed
inverse. The image domain is never identified with a half-plane. -/
private theorem quotientFamily_locally_bounded
    {P : Set ℂ} (hP : IsOpen P) {σ : ℂ → LiZhongQC.BeltramiH}
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hkP : ∀ t ∈ P, LiZhongQC.IsBeltramiCoeff (σ t).val univ k) :
    ∀ t₀ ∈ P, ∀ w₀ ∈ lowerImage (σ 0),
      ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball w₀ ε ⊆ lowerImage (σ 0) ∧
        ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ w ∈ ball w₀ ε, ‖quotientFamily σ t w‖ ≤ M := by
  intro t₀ ht₀ w₀ hw₀
  let x₀ : ℂ := baseInverse (σ 0) w₀
  have hx₀ : x₀ ∈ LiZhongQC.lowerHalf := baseInverse_mapsTo_lowerHalf (σ 0) hw₀
  obtain ⟨ε, hε, htP, -, M, hM⟩ :=
    LiZhongQC.bB_hs_bound hP hk0 hk1 hkP t₀ ht₀ x₀ hx₀
  have hi : ContinuousAt (baseInverse (σ 0)) w₀ :=
    ((baseInverse_differentiableOn (σ 0)).differentiableAt
      ((lowerImage_isOpen (σ 0)).mem_nhds hw₀)).continuousAt
  have hpull : (baseInverse (σ 0)) ⁻¹' ball x₀ ε ∈ 𝓝 w₀ :=
    hi.preimage_mem_nhds (ball_mem_nhds x₀ hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hpull ((lowerImage_isOpen (σ 0)).mem_nhds hw₀))
  refine ⟨min ε δ, lt_min hε hδ, (ball_subset_ball (min_le_left _ _)).trans htP,
    ?_, M, ?_⟩
  · intro w hw
    exact (hδsub ((ball_subset_ball (min_le_right _ _)) hw)).2
  · intro t ht w hw
    exact hM t ((ball_subset_ball (min_le_left _ _)) ht)
      (baseInverse (σ 0) w) (hδsub ((ball_subset_ball (min_le_right _ _)) hw)).1

/-- The actual nonsymmetric normalized quotient family has the correct
Schwarzian variation on its same fixed distorted lower image. -/
theorem hasDerivAt_schwarzian_quotientFamily
    {P : Set ℂ} (hP : IsOpen P) (h0 : (0 : ℂ) ∈ P)
    {σ : ℂ → LiZhongQC.BeltramiH} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hkP : ∀ t ∈ P, LiZhongQC.IsBeltramiCoeff (σ t).val univ k)
    (hhol : ∀ ζ, DifferentiableOn ℂ (fun t => (σ t).val ζ) P)
    {z : ℂ} (hz : z ∈ lowerImage (σ 0)) :
    HasDerivAt (fun t => LiZhongQC.schwarzian (quotientFamily σ t) z)
      (iteratedDeriv 3 (LiZhongQC.ahVar (infinitesimalCoefficient σ)) z) 0 := by
  exact SchwarzianVariation.hasDerivAt_schwarzian_at_identity hP h0
    (lowerImage_isOpen (σ 0))
    (fun w _ => quotientFamily_parameter_differentiableOn hP hk0 hk1 hkP hhol w)
    (fun t _ => quotientFamily_differentiableOn σ t)
    (quotientFamily_locally_bounded hP hk0 hk1 hkP)
    (quotientFamily_zero σ) (fun w _ => hasDerivAt_quotientFamily hP h0 hk0 hk1 hkP hhol w) hz

end LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation
