module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNativeTensorQuadraticFamily
public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMetricLocalSections
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The original smooth symmetric tensor of an actual quadratic differential

The pointwise value uses the existing preferred chart at that point. Its
equality with a fixed-chart formula follows from the given differential's
actual overlap law. Smoothness is then proved in that fixed chart using the
existing nested Hom section criterion, without assuming the chart choice is
smooth. Both tangent slots are the unchanged original real tangent fibres.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Filter Set Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces AtlasMetricConstruction
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The real bilinear form sending v and w to the real part of their product. -/
def quadraticModelReal : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ) Complex.reCLM).comp
    (ContinuousLinearMap.mul ℝ ℂ)

/-- The real bilinear form sending v and w to the imaginary part of their product. -/
def quadraticModelImag : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ) Complex.imCLM).comp
    (ContinuousLinearMap.mul ℝ ℂ)

/-- The continuous real trilinear form sending q, v and w to Re(q * v * w). -/
def quadraticModel : ℂ →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℝ := by
  letI : NormedAddCommGroup (ℂ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  exact @Sub.sub (ℂ →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ContinuousLinearMap.sub
    (Complex.reCLM.smulRight quadraticModelReal)
    (Complex.imCLM.smulRight quadraticModelImag)

private theorem quadraticModel_apply (q v w : ℂ) :
    quadraticModel q v w = (q * v * w).re := by
  change q.re * (v * w).re - q.im * (v * w).im = (q * v * w).re
  simp only [Complex.mul_re, Complex.mul_im]
  ring

/-- A chart-local real bilinear form on the original tangent fibres, with coefficient Q. -/
def quadraticLocalForm
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (p x : X) :
    TangentForm R.toRiemannSurface x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let t := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p
  let c := trivializationAt ℝ (fun _ : X => ℝ) p
  let h := t.continuousLinearMap (RingHom.id ℝ) c
  let T := t.continuousLinearMap (RingHom.id ℝ) h
  exact T.symmL ℝ x (quadraticModel (Q.val p ((chartAt ℂ p) x)))

/-- On a valid preferred chart, the form is Re(Q * Dv * Dw) on all original tangent pairs. -/
theorem quadraticLocalForm_apply
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (p x : X)
    (hx : x ∈ (chosenChart R.toRiemannSurface p).val.source)
    (v w : RealSurfaceTangent R.toRiemannSurface x) :
    quadraticLocalForm R Q p x v w =
      (Q.val p ((chosenChart R.toRiemannSurface p).val x) *
        originalChartDifferential R.toRiemannSurface (chosenChart R.toRiemannSurface p) x v *
        originalChartDifferential R.toRiemannSurface (chosenChart R.toRiemannSurface p) x w).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let t := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p
  let c := trivializationAt ℝ (fun _ : X => ℝ) p
  let h := t.continuousLinearMap (RingHom.id ℝ) c
  let T := t.continuousLinearMap (RingHom.id ℝ) h
  let B := quadraticModel (Q.val p ((chartAt ℂ p) x))
  let : IsNormableSpace ℝ (RealSurfaceTangent R.toRiemannSurface x) :=
    (SmoothSurfaceEquiv.originalChartDifferentialEquiv
      (chosenChart R.toRiemannSurface p) x hx).isNormableSpace
  let F : TangentForm R.toRiemannSurface x := B.bilinearComp
    (t.continuousLinearMapAt ℝ x) (t.continuousLinearMapAt ℝ x)
  have ht : x ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet, chosenChart] using hx
  have hc : x ∈ c.baseSet := by
    have hcx := mem_baseSet_trivializationAt ℝ (fun _ : X => ℝ) x
    simpa only [c, Bundle.Trivial.fiberBundle_trivializationAt'] using hcx
  have hh : x ∈ h.baseSet := ⟨ht, hc⟩
  have hT : x ∈ T.baseSet := ⟨ht, hh⟩
  have hF : T.continuousLinearMapAt ℝ x F = B := by
    ext a b
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ T hT F,
      Trivialization.continuousLinearMap_apply]
    change (h.continuousLinearMapAt ℝ x (F (t.symmL ℝ x a))) b = B a b
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ h hh,
      Trivialization.continuousLinearMap_apply]
    change c.continuousLinearMapAt ℝ x (F (t.symmL ℝ x a) (t.symmL ℝ x b)) = B a b
    simp only [c, Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
    dsimp only [F]
    rw [ContinuousLinearMap.bilinearComp_apply,
      Trivialization.continuousLinearMapAt_symmL t ht,
      Trivialization.continuousLinearMapAt_symmL t ht]
  have hlocal : quadraticLocalForm R Q p x = F := by
    change T.symmL ℝ x B = F
    rw [← hF]
    exact T.symmL_continuousLinearMapAt hT F
  have hD : t.continuousLinearMapAt ℝ x =
      originalChartDifferential R.toRiemannSurface (chosenChart R.toRiemannSurface p) x := by
    have hx' : x ∈ (chartAt ℂ p).source := hx
    have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ p : X → ℂ) x :=
      mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) (chart_mem_atlas ℂ p) hx'
    change (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p).continuousLinearMapAt ℝ x =
      mvfderiv 𝓘(ℝ, ℂ) (chartAt ℂ p : X → ℂ) x
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx',
      tangentBundleCore_coordChange_achart, hd.mvfderiv]
    simp only [writtenInExtChartAt, extChartAt_self_eq, extChartAt_coe,
      modelWithCornersSelf_coe, Function.id_comp]
    ext a
    rfl
  rw [hlocal]
  change B (t.continuousLinearMapAt ℝ x v) (t.continuousLinearMapAt ℝ x w) = _
  rw [hD]
  exact quadraticModel_apply _ _ _

private theorem quadratic_chart_deriv
    (e f : OriginalComplexChart R.toRiemannSurface) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source)
    (v : RealSurfaceTangent R.toRiemannSurface x) :
    originalChartDifferential R.toRiemannSurface f x v =
      deriv (e.val.symm.trans f.val) (e.val x) *
        originalChartDifferential R.toRiemannSurface e x v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let T : ℂ → ℂ := e.val.symm.trans f.val
  have hz : e.val x ∈ (e.val.symm.trans f.val).source := by
    refine ⟨e.val.map_source he, ?_⟩
    simpa only [Set.mem_preimage, OpenPartialHomeomorph.symm_symm,
      e.val.left_inv he] using hf
  have ht : DifferentiableAt ℂ T (e.val x) :=
    (R.toRiemannAtlas.compatible e.val e.property f.val f.property (e.val x) hz).differentiableAt
  have hh := (SmoothSurfaceEquiv.refl R.toRiemannSurface).chartDifferential_intertwines
    e f x he hf v
  change fderiv ℝ T (e.val x) (originalChartDifferential R.toRiemannSurface e x v) =
    originalChartDifferential R.toRiemannSurface f x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : X → X) x v) at hh
  simp only [mfderiv_id, ContinuousLinearMap.id_apply] at hh
  rw [ht.fderiv_restrictScalars ℝ] at hh
  change fderiv ℂ T (e.val x) (originalChartDifferential R.toRiemannSurface e x v) =
    originalChartDifferential R.toRiemannSurface f x v at hh
  rw [fderiv_eq_deriv_mul] at hh
  exact hh.symm

/-- The pointwise real part of Q using the preferred chart at the same original point. -/
def quadraticRaw (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    TangentForm R.toRiemannSurface x := quadraticLocalForm R Q x x

private theorem quadraticRaw_eq_local
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (p x : X)
    (hx : x ∈ (chosenChart R.toRiemannSurface p).val.source) :
    quadraticRaw R Q x = quadraticLocalForm R Q p x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e := chosenChart R.toRiemannSurface x
  let f := chosenChart R.toRiemannSurface p
  have he : x ∈ e.val.source := mem_chart_source ℂ x
  have hf : x ∈ f.val.source := hx
  let t := deriv (e.val.symm.trans f.val) (e.val x)
  have hsource : (chartAt ℂ x).symm (e.val x) ∈ (chartAt ℂ p).source := by
    change e.val.symm (e.val x) ∈ f.val.source
    simpa only [e.val.left_inv he] using hf
  have htransition := Q.property.1.2 p x (e.val x) (e.val.map_source he) hsource
  have hq : Q.val x (e.val x) = Q.val p (f.val x) * t ^ 2 := by
    have hcoord : LiZhongQC.chartTransition p x (e.val x) = f.val x := by
      change f.val (e.val.symm (e.val x)) = f.val x
      rw [e.val.left_inv he]
    have hderiv : deriv (LiZhongQC.chartTransition p x) (e.val x) = t := rfl
    rw [hcoord, hderiv] at htransition
    simpa only [zpow_ofNat, pow_zero, mul_one] using htransition
  have hD (v : RealSurfaceTangent R.toRiemannSurface x) :
      originalChartDifferential R.toRiemannSurface f x v =
        t * originalChartDifferential R.toRiemannSurface e x v :=
    quadratic_chart_deriv R e f x he hf v
  ext v w
  change quadraticLocalForm R Q x x v w = quadraticLocalForm R Q p x v w
  rw [quadraticLocalForm_apply R Q x x he, quadraticLocalForm_apply R Q p x hf]
  change (Q.val x (e.val x) * originalChartDifferential R.toRiemannSurface e x v *
      originalChartDifferential R.toRiemannSurface e x w).re =
    (Q.val p (f.val x) * originalChartDifferential R.toRiemannSurface f x v *
      originalChartDifferential R.toRiemannSurface f x w).re
  rw [hq, hD v, hD w]
  congr 1
  ring

/-- The bilinear form determined by Q is a smooth section of the original tensor bundle. -/
theorem quadraticRaw_contMDiff
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
        (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
          TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) x (quadraticRaw R Q x)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : NormedAddCommGroup (ℂ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  dsimp only
  intro x₀
  let e := chosenChart R.toRiemannSurface x₀
  let t := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) x₀
  let c := trivializationAt ℝ (fun _ : X => ℝ) x₀
  let h := t.continuousLinearMap (RingHom.id ℝ) c
  let T := t.continuousLinearMap (RingHom.id ℝ) h
  have he : x₀ ∈ e.val.source := mem_chart_source ℂ x₀
  have hcbase : c.baseSet = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    have hy := mem_baseSet_trivializationAt ℝ (fun _ : X => ℝ) y
    simpa only [c, Bundle.Trivial.fiberBundle_trivializationAt'] using hy
  have hbase : T.baseSet = e.val.source := by
    simp only [T, h, Trivialization.baseSet_continuousLinearMap,
      hcbase, t, TangentBundle.trivializationAt_baseSet, e, chosenChart,
      Set.inter_univ, Set.inter_self]
  have hT₀ : x₀ ∈ T.baseSet := hbase.symm ▸ he
  have hq : ContDiffOn ℝ ∞ (Q.val x₀) e.val.target :=
    ((Q.property.2 x₀).contDiffOn e.val.open_target).restrict_scalars ℝ
  have hqAt : ContDiffAt ℝ ∞ (Q.val x₀) (e.val x₀) :=
    hq.contDiffAt (e.val.open_target.mem_nhds (e.val.map_source he))
  have heAt : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.val x₀ :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) he
  have hcoord : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun y => Q.val x₀ (e.val y)) x₀ := hqAt.comp_contMDiffAt heAt
  have hquad : ContDiff ℝ ∞ (fun q : ℂ => quadraticModel q) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℂ)
      (F := ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (n := ∞)
      (quadraticModel : ℂ →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  have hmodel : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun y => quadraticModel (Q.val x₀ (e.val y))) x₀ :=
    hquad.comp_contMDiffAt hcoord
  apply (T.contMDiffAt_section_iff hT₀).mpr
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [e.val.open_source.mem_nhds he] with y hy
  rw [quadraticRaw_eq_local R Q x₀ y hy]
  change (T ⟨y, T.symmL ℝ y (quadraticModel (Q.val x₀ (e.val y)))⟩).2 = _
  have hTy : y ∈ T.baseSet := hbase.symm ▸ hy
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ T hTy]
  exact T.continuousLinearMapAt_symmL hTy (quadraticModel (Q.val x₀ (e.val y)))

/-- The actual original smooth symmetric tensor with real part equal to Q. -/
def quadraticDifferentialTensor (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    SmoothSymmetricTwoTensor R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  refine ⟨⟨quadraticRaw R Q, quadraticRaw_contMDiff R Q⟩, ?_⟩
  simp only [symmetricTwoTensorSubmodule]
  intro x v w
  change quadraticLocalForm R Q x x v w = quadraticLocalForm R Q x x w v
  have hx : x ∈ (chosenChart R.toRiemannSurface x).val.source := mem_chart_source ℂ x
  simp only [quadraticLocalForm_apply R Q x x hx]
  congr 1
  ring

/-- In every valid preferred original chart the tensor uses exactly Q's
coefficient and both actual original chart differentials. -/
theorem quadraticDifferentialTensor_apply
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (p x : X)
    (hx : x ∈ (chosenChart R.toRiemannSurface p).val.source)
    (v w : RealSurfaceTangent R.toRiemannSurface x) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    (quadraticDifferentialTensor R Q).val.toFun x v w =
      (Q.val p ((chosenChart R.toRiemannSurface p).val x) *
        originalChartDifferential R.toRiemannSurface (chosenChart R.toRiemannSurface p) x v *
        originalChartDifferential R.toRiemannSurface (chosenChart R.toRiemannSurface p) x w).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  change quadraticRaw R Q x v w = _
  rw [quadraticRaw_eq_local R Q p x hx]
  exact quadraticLocalForm_apply R Q p x hx v w

end LowDimensionalTopology.Geometry.Teichmuller
