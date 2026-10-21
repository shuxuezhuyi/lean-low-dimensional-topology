/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HypercycleDistance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine positive-radius H ball has precisely the actual metric circle as its frontier. -/
theorem hMetric_ball_frontier (p : ℍ) (r : ℝ) (hr : 0<r) :
    frontier (Metric.ball p r)=Metric.sphere p r := by
  apply Set.Subset.antisymm
  · exact Metric.frontier_ball_subset_sphere
  · intro z hz
    have hzp : z≠p := by intro he;rw [he] at hz;change dist p p=r at hz;rw [dist_self] at hz;linarith
    obtain ⟨L,hLp,hLz⟩ := exists_halfPlaneLine_through p z hzp.symm
    obtain ⟨γ,hγ,hrange⟩ := L.exists_isometric_param
    obtain ⟨s,hs⟩ : ∃s : ℝ,γ s=p := by rw [← hrange] at hLp;exact hLp
    obtain ⟨t,ht⟩ : ∃t : ℝ,γ t=z := by rw [← hrange] at hLz;exact hLz
    have hst : |t-s|=r := by
      change dist z p=r at hz
      rw [← hs,← ht,hγ.dist_eq,Real.dist_eq] at hz
      exact hz
    have hcl : z ∈ closure (Metric.ball p r) := by
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      let δ := min (ε/(2*r)) (1/2 : ℝ)
      have hd : 0<δ := lt_min (div_pos hε (by positivity)) (by norm_num)
      have hd1 : δ<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hde : δ*r≤ε/2 := by
        have hδ : δ≤ε/(2*r) := min_le_left _ _
        have he := (le_div_iff₀ (by positivity : (0:ℝ)<2*r)).mp hδ
        nlinarith [he]
      refine ⟨γ ((1-δ)*t+δ*s),?_,?_⟩
      · change dist (γ ((1-δ)*t+δ*s)) p<r
        rw [← hs,hγ.dist_eq,Real.dist_eq]
        have he : (1-δ)*t+δ*s-s=(1-δ)*(t-s) := by ring
        rw [he,abs_mul,abs_of_pos (sub_pos.mpr hd1),hst]
        nlinarith [mul_pos hd hr]
      · rw [← ht,hγ.dist_eq,Real.dist_eq]
        have he : t-((1-δ)*t+δ*s)=δ*(t-s) := by ring
        rw [he,abs_mul,abs_of_pos hd,hst]
        linarith
    rw [frontier,Metric.isOpen_ball.interior_eq]
    refine ⟨hcl,?_⟩
    change ¬dist z p<r
    change dist z p=r at hz
    rw [hz]
    exact lt_irrefl _

/-- A singleton has no relative interior in the genuine hyperbolic plane. -/
theorem h_frontier_singleton (p : ℍ) : frontier ({p} : Set ℍ)={p} := by
  have hint : interior ({p} : Set ℍ)=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzp : z=p := Set.mem_singleton_iff.mp (interior_subset hz)
    subst z
    have he : interior ({p} : Set ℍ)={p} :=
      Set.Subset.antisymm interior_subset (Set.singleton_subset_iff.mpr hz)
    have hopen : IsOpen ({p} : Set ℍ) := he ▸ isOpen_interior
    have him := UpperHalfPlane.isOpenMap_im _ hopen
    rw [Set.image_singleton] at him
    exact not_isOpen_singleton p.im him
  rw [frontier,isClosed_singleton.closure_eq,hint,Set.sdiff_empty]

/-- The complete native tube frontier, proved by actual horizontal perturbations. -/
theorem imaginaryAxis_distanceSublevel_frontier (r : ℝ) (hr : 0<r) :
    frontier ((HalfPlaneLine.vertical 0).distanceSublevel r)=
      {z : ℍ | (HalfPlaneLine.vertical 0).pointDist z=r} := by
  have hp : Continuous (HalfPlaneLine.vertical 0).pointDist := Metric.continuous_infDist_pt _
  have hopen : IsOpen ((HalfPlaneLine.vertical 0).distanceSublevel r) := isOpen_lt hp continuous_const
  apply Set.Subset.antisymm
  · exact frontier_lt_subset_eq hp continuous_const
  · intro z hz
    have hsz := congrArg Real.sinh hz
    rw [verticalLine_pointDist_sinh,sub_zero] at hsz
    let γ : ℝ → ℍ := fun t=>metricProbe (t*z.re) z.im z.im_pos
    have hγ : Continuous γ := by
      apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
      change Continuous (fun t : ℝ=>(⟨t*z.re,z.im⟩ : ℂ))
      have he : (fun t : ℝ=>(⟨t*z.re,z.im⟩ : ℂ))=
          (fun t : ℝ=>((t*z.re : ℝ) : ℂ)+(z.im : ℂ)*Complex.I) := by
        funext t
        apply Complex.ext <;> simp
      rw [he]
      fun_prop
    have hγ1 : γ 1=z := by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp [γ,metricProbe]
    have himage : γ '' Ioo (0:ℝ) 1 ⊆ (HalfPlaneLine.vertical 0).distanceSublevel r := by
      rintro _ ⟨t,ht,rfl⟩
      change (HalfPlaneLine.vertical 0).pointDist (γ t)<r
      apply Real.sinh_lt_sinh.mp
      rw [verticalLine_pointDist_sinh,sub_zero]
      change |t*z.re|/z.im<Real.sinh r
      rw [abs_mul,abs_of_pos ht.1]
      have he : t*|z.re|/z.im=t*Real.sinh r := by rw [← hsz];ring
      rw [he]
      have hs : 0<Real.sinh r := Real.sinh_pos_iff.mpr hr
      nlinarith [mul_pos (sub_pos.mpr ht.2) hs]
    have h1 : (1:ℝ)∈closure (Ioo (0:ℝ) 1) := by rw [closure_Ioo zero_ne_one];simp
    have hcl : z∈closure ((HalfPlaneLine.vertical 0).distanceSublevel r) := by
      rw [←hγ1]
      exact closure_mono himage (mem_closure_image hγ.continuousAt h1)
    rw [frontier,hopen.interior_eq]
    refine ⟨hcl,?_⟩
    change ¬(HalfPlaneLine.vertical 0).pointDist z<r
    rw [hz]
    exact lt_irrefl _

/-- The genuine distance tube about any actual h-line has its full equidistant frontier. -/
theorem HalfPlaneLine.distanceSublevel_frontier (L : HalfPlaneLine) (r : ℝ) (hr : 0<r) :
    frontier (L.distanceSublevel r)={z : ℍ | L.pointDist z=r} := by
  obtain ⟨g,_hg,hgL⟩ := L.exists_normalizer
  let H : ℍ ≃ᵢ ℍ := {toEquiv:=MulAction.toPerm g,isometry_toFun:=realGL_isometry g}
  have hline : (fun z : ℍ=>g • z) '' L.carrier=(HalfPlaneLine.vertical 0).carrier := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [hgL] at hw
      exact hw
    · intro hz
      change z.re=0 at hz
      refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
      rw [hgL]
      change (g • (g⁻¹ • z)).re=0
      simpa only [smul_inv_smul] using hz
  have hsub := L.distanceSublevel_image_isometry (.vertical 0) (fun z=>g • z) (realGL_isometry g) hline r
  have hpd (z : ℍ) := L.pointDist_isometry_image (.vertical 0) (fun z=>g • z) (realGL_isometry g) hline z
  have hlevel : H '' {z : ℍ | L.pointDist z=r}={z : ℍ | (HalfPlaneLine.vertical 0).pointDist z=r} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      change (HalfPlaneLine.vertical 0).pointDist (g • w)=r
      rw [hpd]
      exact hw
    · intro hz
      refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
      change L.pointDist (g⁻¹ • z)=r
      rw [←hpd,smul_inv_smul]
      exact hz
  apply H.injective.image_injective
  change H.toHomeomorph '' frontier (L.distanceSublevel r)=H.toHomeomorph '' {z | L.pointDist z=r}
  rw [H.toHomeomorph.image_frontier]
  change frontier ((fun z : ℍ=>g • z) '' L.distanceSublevel r)=H '' {z | L.pointDist z=r}
  rw [hsub,imaginaryAxis_distanceSublevel_frontier r hr,hlevel]

end LowDimensionalTopology.Geometry.Hyperbolic
