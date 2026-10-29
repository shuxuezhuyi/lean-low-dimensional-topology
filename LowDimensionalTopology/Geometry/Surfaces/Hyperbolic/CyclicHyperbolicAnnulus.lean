module

public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.CrossRatioDistance
public import Mathlib.Algebra.Group.End

/-!
# Genuine annulus coordinates for cyclic hyperbolic coverings

The annulus has its ordinary complex topology and inherited plane atlas. Its
coordinate is the actual exponential of the principal logarithm after a real
Möbius normalization; equality of its fibers is proved, not assumed conformal.

The logarithmic coordinate, complete image/fiber computation and hyperbolic
normal form reuse Wu Xiaobin's Li-Zhong-QC-formalization, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`, Apache-2.0, through the existing
attributed local source modules.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry
open Hyperbolic Mobius Fuchsian DiscreteGroups

/-- The ordinary circular annulus, with inner radius exactly one. -/
def roundAnnulusSurface (r : ℝ) (hr : 1 < r) :
    RiemannSurface (LiZhongQC.annulus 1 r) where
  toRiemannAtlas := complexPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph
    (Subtype.val : LiZhongQC.annulus 1 r → ℂ)
    (LiZhongQC.isOpen_annulus 1 r).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  t2Space := inferInstance
  connectedSpace := Subtype.connectedSpace (show IsConnected (LiZhongQC.annulus 1 r) from by
    refine ⟨⟨(((1 + r) / 2 : ℝ) : ℂ), ?_⟩,
      LiZhongQC.isPreconnected_annulus (by norm_num : (0 : ℝ) ≤ 1)⟩
    change 1 < ‖(((1 + r) / 2 : ℝ) : ℂ)‖ ∧ ‖(((1 + r) / 2 : ℝ) : ℂ)‖ < r
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    constructor <;> linarith)

/-- The finite outer radius of the quotient by `z ↦ λ² z`. -/
def dilationAnnulusRadius (lam : ℝ) : ℝ :=
  Real.exp (2 * Real.pi ^ 2 / Real.log (lam ^ 2))

theorem dilationAnnulusRadius_one_lt {lam : ℝ} (hlam : 1 < lam) :
    1 < dilationAnnulusRadius lam := by
  have hL : 0 < Real.log (lam ^ 2) := Real.log_pos (by nlinarith)
  change 1 < Real.exp (2 * Real.pi ^ 2 / Real.log (lam ^ 2))
  have ht : 0 < 2 * Real.pi ^ 2 / Real.log (lam ^ 2) := div_pos (by positivity) hL
  simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr ht

/-- The actual logarithmic annulus coordinate on the upper half-plane. -/
def dilationAnnulusCoordinate (lam : ℝ) (z : ℂ) : ℂ :=
  (dilationAnnulusRadius lam : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * Complex.log z / Real.log (lam ^ 2))

theorem dilationAnnulusCoordinate_image {lam : ℝ} (hlam : 1 < lam) :
    dilationAnnulusCoordinate lam '' LiZhongQC.upperHalf =
      LiZhongQC.annulus 1 (dilationAnnulusRadius lam) :=
  (LiZhongQC.s30w_phi_facts hlam).2

theorem dilationAnnulusCoordinate_fiber {lam : ℝ} (hlam : 1 < lam) (z w : ℍ) :
    dilationAnnulusCoordinate lam z = dilationAnnulusCoordinate lam w ↔
      ∃ n : ℤ, (w : ℂ) = ((lam : ℂ) ^ 2) ^ n * (z : ℂ) :=
  (LiZhongQC.s30w_phi_facts hlam).1 z z.im_pos w w.im_pos

/-- The coordinate really takes values in the ordinary annulus. -/
def dilationAnnulusMap (lam : ℝ) (hlam : 1 < lam) :
    ℍ → LiZhongQC.annulus 1 (dilationAnnulusRadius lam) := fun z =>
  ⟨dilationAnnulusCoordinate lam z,
    dilationAnnulusCoordinate_image hlam ▸ Set.mem_image_of_mem _ z.im_pos⟩

theorem dilationAnnulusMap_surjective {lam : ℝ} (hlam : 1 < lam) :
    Function.Surjective (dilationAnnulusMap lam hlam) := by
  intro w
  have hw : (w : ℂ) ∈ dilationAnnulusCoordinate lam '' LiZhongQC.upperHalf := by
    rw [dilationAnnulusCoordinate_image hlam]
    exact w.property
  obtain ⟨z, hz, hzw⟩ := hw
  exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩

/-- Analyticity uses the actual inherited annulus atlas and the original
half-plane manifold, without transporting a complex structure along the map. -/
theorem dilationAnnulusMap_analytic {lam : ℝ} (hlam : 1 < lam) :
    RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      (roundAnnulusSurface (dilationAnnulusRadius lam)
        (dilationAnnulusRadius_one_lt hlam)).toRiemannAtlas
      (dilationAnnulusMap lam hlam) := by
  have hd : DifferentiableOn ℂ (dilationAnnulusCoordinate lam) LiZhongQC.upperHalf :=
    LiZhongQC.s30w_phi_differentiableOn _ _
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℍ => dilationAnnulusCoordinate lam z) := by
    apply UpperHalfPlane.mdifferentiable_iff.mpr
    apply hd.congr
    intro z hz
    change dilationAnnulusCoordinate lam (UpperHalfPlane.ofComplex z : ℂ) =
      dilationAnnulusCoordinate lam z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have ha : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      complexPlaneRiemannSurface.toRiemannAtlas
      (fun z : ℍ => dilationAnnulusCoordinate lam z) :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hmd)
  apply RiemannAnalyticMap.of_comp_localHomeomorph
    (complexPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph_projection_analytic
      (Subtype.val : LiZhongQC.annulus 1 (dilationAnnulusRadius lam) → ℂ)
      (LiZhongQC.isOpen_annulus 1 _).isOpenEmbedding_subtypeVal.isLocalHomeomorph)
    (LiZhongQC.isOpen_annulus 1 _).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (hmd.continuous.subtype_mk _) ha

/-- A given original analytic covering with precisely the dilation orbits as
fibers descends to an actual annulus biholomorphism, with its literal formula
on the SAME projection. -/
theorem annulusHomeomorph_of_dilation_cover
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X)
    (p : ℍ → X) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (ha : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ) R.toRiemannAtlas p)
    (lam : ℝ) (hlam : 1 < lam)
    (hfiber : ∀ z w : ℍ, p z = p w ↔
      ∃ n : ℤ, (w : ℂ) = ((lam : ℂ) ^ 2) ^ n * (z : ℂ)) :
    ∃ e : X ≃ₜ LiZhongQC.annulus 1 (dilationAnnulusRadius lam),
      RiemannAnalyticMap R.toRiemannAtlas
        (roundAnnulusSurface (dilationAnnulusRadius lam)
          (dilationAnnulusRadius_one_lt hlam)).toRiemannAtlas e ∧
      ∀ z : ℍ, (e (p z) : ℂ) = dilationAnnulusCoordinate lam z := by
  let P := dilationAnnulusMap lam hlam
  have hP (z w : ℍ) : p z = p w ↔ P z = P w := by
    rw [hfiber, Subtype.ext_iff]
    exact (dilationAnnulusCoordinate_fiber hlam z w).symm
  let f : X → LiZhongQC.annulus 1 (dilationAnnulusRadius lam) :=
    fun x => P (Function.surjInv hs x)
  have hcomm (z : ℍ) : f (p z) = P z :=
    (hP _ z).mp (Function.surjInv_eq hs (p z))
  have hcomp : f ∘ p = P := funext hcomm
  have hfc : Continuous f := by
    apply (hp.isQuotientMap hs).continuous_iff.mpr
    rw [hcomp]
    exact (dilationAnnulusMap_analytic hlam).continuous
  have hfa : RiemannAnalyticMap R.toRiemannAtlas
      (roundAnnulusSurface (dilationAnnulusRadius lam)
        (dilationAnnulusRadius_one_lt hlam)).toRiemannAtlas f := by
    apply RiemannAnalyticMap.of_comp_surjective_localHomeomorph ha
      hp.isLocalHomeomorph hs hfc
    rw [hcomp]
    exact dilationAnnulusMap_analytic hlam
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨z, rfl⟩ := hs x
      obtain ⟨w, rfl⟩ := hs y
      exact (hP z w).mpr ((hcomm z).symm.trans (hxy.trans (hcomm w)))
    · intro w
      obtain ⟨z, hz⟩ := dilationAnnulusMap_surjective hlam w
      exact ⟨p z, (hcomm z).trans hz⟩
  exact ⟨hfa.toHomeomorph hbij, hfa, fun z => congrArg Subtype.val (hcomm z)⟩

private theorem realSL_smul_analytic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ) (RiemannAtlas.ofManifold ℍ)
      (fun z : ℍ => A • z) :=
  riemannAnalyticMap_of_contMDiff_ofManifold
    (LiZhongQC.k22u_mdifferentiable_contMDiff (LiZhongQC.s27t_mdifferentiable_smul A))

private theorem coe_pow_smul_of_coe_smul
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℂ)
    (hA : ∀ z : ℍ, ((A • z : ℍ) : ℂ) = k * (z : ℂ)) (n : ℕ) (z : ℍ) :
    ((A ^ n • z : ℍ) : ℂ) = k ^ n * (z : ℂ) := by
  induction n with
  | zero => simp only [pow_zero, one_smul, one_mul]
  | succ n ih =>
    rw [pow_succ', mul_smul, hA, ih, pow_succ']
    ring

private theorem coe_zpow_smul_of_coe_smul
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℂ) (hk : k ≠ 0)
    (hA : ∀ z : ℍ, ((A • z : ℍ) : ℂ) = k * (z : ℂ)) (n : ℤ) (z : ℍ) :
    ((A ^ n • z : ℍ) : ℂ) = k ^ n * (z : ℂ) := by
  have hinv (w : ℍ) : ((A⁻¹ • w : ℍ) : ℂ) = k⁻¹ * (w : ℂ) := by
    have h := hA (A⁻¹ • w)
    rw [smul_inv_smul] at h
    calc
      ((A⁻¹ • w : ℍ) : ℂ) = k⁻¹ * (k * ((A⁻¹ • w : ℍ) : ℂ)) :=
        (inv_mul_cancel_left₀ hk _).symm
      _ = k⁻¹ * (w : ℂ) := congrArg (fun v : ℂ => k⁻¹ * v) h.symm
  cases n with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
      coe_pow_smul_of_coe_smul A k hA n z
  | negSucc n =>
    simpa only [zpow_negSucc, inv_pow] using
      coe_pow_smul_of_coe_smul A⁻¹ k⁻¹ hinv (n + 1) z

/-- Every original analytic covering with actual orbits of a hyperbolic
matrix as fibers has a genuine annulus coordinate. The normalizing matrix is
proved to exist, and the formula retains the original projection `p`. -/
theorem annulusHomeomorph_of_hyperbolic_cyclic_cover
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X)
    (p : ℍ → X) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (ha : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ) R.toRiemannAtlas p)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : LiZhongQC.IsHyperbolic A)
    (hfiber : ∀ z w : ℍ, p z = p w ↔ ∃ n : ℤ, w = A ^ n • z) :
    ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ) (hlam : 1 < lam)
      (e : X ≃ₜ LiZhongQC.annulus 1 (dilationAnnulusRadius lam)),
      RiemannAnalyticMap R.toRiemannAtlas
        (roundAnnulusSurface (dilationAnnulusRadius lam)
          (dilationAnnulusRadius_one_lt hlam)).toRiemannAtlas e ∧
      Real.log (lam ^ 2) = LiZhongQC.translationLength A ∧
      ∀ z : ℍ, (e (p z) : ℂ) = dilationAnnulusCoordinate lam (B • z : ℍ) := by
  obtain ⟨B, lam, hlam, hlength, hBA⟩ := LiZhongQC.s30w_conj_dilation hA
  let C := B * A * B⁻¹
  have hk : (lam : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by linarith))
  have hC (n : ℤ) (z : ℍ) :
      ((C ^ n • z : ℍ) : ℂ) = ((lam : ℂ) ^ 2) ^ n * (z : ℂ) := by
    apply coe_zpow_smul_of_coe_smul C ((lam : ℂ) ^ 2) hk
    intro w
    simpa only [C, Complex.ofReal_pow] using hBA w
  let q : ℍ → X := p ∘ (Homeomorph.smul B⁻¹)
  have hq : IsCoveringMap q := hp.comp_homeomorph (Homeomorph.smul B⁻¹)
  have hqs : Function.Surjective q := hs.comp (Homeomorph.smul B⁻¹).surjective
  have hqa : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ) R.toRiemannAtlas q :=
    ha.comp (realSL_smul_analytic B⁻¹)
  have hqfiber (z w : ℍ) : q z = q w ↔
      ∃ n : ℤ, (w : ℂ) = ((lam : ℂ) ^ 2) ^ n * (z : ℂ) := by
    change p (B⁻¹ • z) = p (B⁻¹ • w) ↔ _
    rw [hfiber]
    constructor
    · rintro ⟨n, hn⟩
      have hw : w = C ^ n • z := by
        dsimp only [C]
        rw [conj_zpow, mul_smul, mul_smul, ← hn, smul_inv_smul]
      exact ⟨n, (congrArg UpperHalfPlane.coe hw).trans (hC n z)⟩
    · rintro ⟨n, hn⟩
      have hw : w = C ^ n • z := UpperHalfPlane.ext (hn.trans (hC n z).symm)
      refine ⟨n, ?_⟩
      dsimp only [C] at hw
      rw [conj_zpow, mul_smul, mul_smul] at hw
      simpa only [inv_smul_smul] using congrArg (fun v : ℍ => B⁻¹ • v) hw
  obtain ⟨e, he, hcomm⟩ := annulusHomeomorph_of_dilation_cover R q hq hqs hqa lam hlam hqfiber
  refine ⟨B, lam, hlam, e, he, hlength, ?_⟩
  intro z
  simpa only [q, Function.comp_apply, Homeomorph.smul_apply, inv_smul_smul] using hcomm (B • z)

/-- Every original hyperbolic surface whose ACTUAL model group is generated
by an ACTUAL hyperbolic Mobius map is biholomorphic to an ordinary finite
annulus. The resulting coordinate is expressed on the original half-plane
projection, with no assumed conformal identification or matrix-sign lift. -/
theorem HyperbolicSurfaceModel.annulusHomeomorph_of_hyperbolic_cyclic_group
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (f : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusHyperbolic f) (hgroup : M.group = Subgroup.zpowers f) :
    ∃ (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ) (hlam : 1 < lam)
      (e : X ≃ₜ LiZhongQC.annulus 1 (dilationAnnulusRadius lam)),
      realSLMobius A = cayleyMobius⁻¹ * f * cayleyMobius ∧
      RiemannAnalyticMap R.toRiemannAtlas
        (roundAnnulusSurface (dilationAnnulusRadius lam)
          (dilationAnnulusRadius_one_lt hlam)).toRiemannAtlas e ∧
      Real.log (lam ^ 2) = LiZhongQC.translationLength A ∧
      ∀ z : ℍ, (e (M.halfPlaneCover z) : ℂ) = dilationAnnulusCoordinate lam (B • z : ℍ) := by
  let D := unitDiscMobiusInvariantDomain M.group M.invariant
  let : MulAction M.group extendedUnitDisc := mobiusDomainAction D
  let E : ℍ ≃ₜ extendedUnitDisc := cayleyHomeomorph.trans discFiniteHomeomorph.symm
  have hEcoe (z : ℍ) : (E z).val = cayleyMobius.val (z : ℂ) := by
    have hchart : discFiniteChart (E z) = (halfPlaneToDisc z : ℂ) := by
      exact congrArg Subtype.val (discFiniteHomeomorph.apply_symm_apply (cayleyHomeomorph z))
    exact (discFiniteChart_coe (E z)).symm.trans
      ((congrArg (fun w : ℂ => (w : Mobius.ExtendedComplex)) hchart).trans
        (extendedCayley_halfPlane z).symm)
  have hfmem : f ∈ M.group := hgroup.symm ▸ Subgroup.mem_zpowers f
  let fg : M.group := ⟨f, hfmem⟩
  let P : FuchsianDisc M.group :=
    ⟨extendedUnitDisc, extendedUnitDisc_isComplexOpenDisc, M.invariant, M.discontinuous⟩
  have hfdisc : f.val '' extendedUnitDisc = extendedUnitDisc := P.image_eq fg
  have hcinv : cayleyMobius⁻¹.val '' extendedUnitDisc = openHalfPlaneSet := by
    rw [← cayleyMobius_image_openHalfPlane, Set.image_image]
    change (fun z : Mobius.ExtendedComplex => cayleyMobius⁻¹ • (cayleyMobius • z)) ''
      openHalfPlaneSet = openHalfPlaneSet
    simp only [inv_smul_smul, Set.image_id']
  let f₀ := cayleyMobius⁻¹ * f * cayleyMobius
  have hf₀pres : f₀.val '' openHalfPlaneSet = openHalfPlaneSet := by
    calc
      _ = cayleyMobius⁻¹.val '' (f.val '' (cayleyMobius.val '' openHalfPlaneSet)) := by
        simp only [f₀, Set.image_image, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_def]
      _ = openHalfPlaneSet := by rw [cayleyMobius_image_openHalfPlane, hfdisc, hcinv]
  obtain ⟨A, hA⟩ := mobius_preserves_halfPlane_exists_SL f₀ hf₀pres
  have hAhypMobius : Mobius.MobiusHyperbolic (realSLMobius A) := by
    rw [hA]
    simpa only [f₀, inv_inv] using mobiusHyperbolic_conjugation_forward f cayleyMobius⁻¹ hf
  have hAsq := (realSLMobius_hyperbolic_iff A hAhypMobius.1.1).mp hAhypMobius
  have hAhyp : LiZhongQC.IsHyperbolic A := by
    have htr : Matrix.trace A.val = A 0 0 + A 1 1 :=
      Matrix.trace_fin_two A.val
    rw [htr] at hAsq
    change 2 < |A 0 0 + A 1 1|
    nlinarith [sq_abs (A 0 0 + A 1 1), abs_nonneg (A 0 0 + A 1 1)]
  have hEact (z : ℍ) : E (A • z) = fg • E z := by
    apply Subtype.ext
    change (E (A • z)).val = f.val (E z).val
    rw [hEcoe, hEcoe]
    calc
      _ = cayleyMobius.val ((realSLMobius A).val (z : ℂ)) :=
        congrArg cayleyMobius.val (realSLMobius_action A z).symm
      _ = _ := by
        rw [hA]
        change cayleyMobius • ((cayleyMobius⁻¹ * f * cayleyMobius) •
          ((z : ℂ) : Mobius.ExtendedComplex)) =
          f • (cayleyMobius • ((z : ℂ) : Mobius.ExtendedComplex))
        simp only [mul_smul, smul_inv_smul]
  let φ : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Equiv.Perm extendedUnitDisc :=
    E.toEquiv.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) ℝ) ℍ)
  let ψ := MulAction.toPermHom M.group extendedUnitDisc
  have hφ : φ A = ψ fg := by
    apply Equiv.ext
    intro z
    change E (A • E.symm z) = fg • z
    rw [hEact, E.apply_symm_apply]
  have hEpow (n : ℤ) (z : ℍ) : E (A ^ n • z) = fg ^ n • E z := by
    have hpow : φ (A ^ n) = ψ (fg ^ n) := by rw [map_zpow, map_zpow, hφ]
    have he := congrArg (fun q : Equiv.Perm extendedUnitDisc => q (E z)) hpow
    change E (A ^ n • E.symm (E z)) = fg ^ n • E z at he
    simpa only [E.symm_apply_apply] using he
  have hproj (z w : ℍ) : M.halfPlaneCover z = M.halfPlaneCover w ↔
      ∃ g : M.group, g • E z = E w := by
    constructor
    · intro hzw
      change M.homeomorph.symm (mobiusDomainProjection D (E z)) =
        M.homeomorph.symm (mobiusDomainProjection D (E w)) at hzw
      exact Quotient.exact (M.homeomorph.symm.injective hzw.symm)
    · rintro ⟨g, hg⟩
      change M.homeomorph.symm (mobiusDomainProjection D (E z)) =
        M.homeomorph.symm (mobiusDomainProjection D (E w))
      have hquot : mobiusDomainProjection D (E w) = mobiusDomainProjection D (E z) := by
        apply Quotient.sound
        exact ⟨g, hg⟩
      exact congrArg M.homeomorph.symm hquot.symm
  have hfiber (z w : ℍ) : M.halfPlaneCover z = M.halfPlaneCover w ↔
      ∃ n : ℤ, w = A ^ n • z := by
    rw [hproj]
    constructor
    · rintro ⟨g, hg⟩
      have hgmem : (g : Mobius.complexMobiusGroup) ∈ Subgroup.zpowers f := by
        simpa only [hgroup] using g.property
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgmem
      have hgn : g = fg ^ n := by
        apply Subtype.ext
        simpa only [Subgroup.coe_zpow, fg] using hn.symm
      refine ⟨n, E.injective ?_⟩
      exact hg.symm.trans ((congrArg (fun u : M.group => u • E z) hgn).trans
        (hEpow n z).symm)
    · rintro ⟨n, rfl⟩
      exact ⟨fg ^ n, (hEpow n z).symm⟩
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨_Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have ha : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      R.toRiemannAtlas M.halfPlaneCover := by
    have h := riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hp.2.1)
    rw [RiemannAtlas.ofManifold_toChartedSpace R.toRiemannAtlas] at h
    exact h
  obtain ⟨B, lam, hlam, e, he, hlength, hcomm⟩ :=
    annulusHomeomorph_of_hyperbolic_cyclic_cover R M.halfPlaneCover
      M.halfPlaneCover_covering M.halfPlaneCover_surjective ha A hAhyp hfiber
  exact ⟨A, B, lam, hlam, e, hA, he, hlength, hcomm⟩

end LowDimensionalTopology.Geometry.Surfaces
