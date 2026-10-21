/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.CrossRatio
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyBoundaryGroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Ball.RadialDistance
public import Mathlib.Topology.Perfect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Module.Connected
/-!
# Quantitative chordal distortion

Cross-ratio preservation yields the two-omission estimate on genuine open
domains. Clearance from the complement gives a uniform local Lipschitz
constant. On the chordal sphere, the distance to the complement agrees
with the distance to the frontier. The optimal global chordal Lipschitz
constant is the exponential of the actual Poincaré-extension displacement
in the native upper-half-space path metric. Connected punctured-domain
translation examples prove that the dimension-uniform coefficient 8 in the
two-omission estimate is optimal (and is optimal in every dimension at least 2).
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Set Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

theorem chordalDist_nonneg (x y : ExtendedEuclidean n) : 0 ≤ chordalDist x y := dist_nonneg

theorem chordalDist_le_two (x y : ExtendedEuclidean n) : chordalDist x y ≤ 2 := by
  have hx := (stereographicHomeomorph n x).property
  have hy := (stereographicHomeomorph n y).property
  rw [Metric.mem_sphere,dist_zero_right] at hx hy
  change dist ((stereographicHomeomorph n x).val) ((stereographicHomeomorph n y).val) ≤ 2
  calc
    _ ≤ ‖(stereographicHomeomorph n x).val‖ + ‖(stereographicHomeomorph n y).val‖ :=
      by rw [dist_eq_norm]; exact norm_sub_le _ _
    _ = 2 := by rw [hx,hy]; norm_num

theorem generalMobius_distortion_product (f : ExtendedHomeomorph n) (hf : f ∈ generalMobiusGroup n)
    (x y a b : ExtendedEuclidean n) (hd : FourDistinct x y a b) :
    chordalDist (f x) (f y)^2 * (chordalDist x a * chordalDist x b * chordalDist y a * chordalDist y b) *
      chordalDist (f a) (f b)^2 =
      chordalDist x y^2 * chordalDist a b^2 *
        (chordalDist (f x) (f a) * chordalDist (f x) (f b) * chordalDist (f y) (f a) * chordalDist (f y) (f b)) := by
  have h1 := generalMobius_preservesRealCrossRatios f hf x y a b hd
  have hd' : FourDistinct x y b a := ⟨hd.1,hd.2.2.1,hd.2.1,hd.2.2.2.2.1,hd.2.2.2.1,hd.2.2.2.2.2.symm⟩
  have h2 := generalMobius_preservesRealCrossRatios f hf x y b a hd'
  simp only [realCrossRatio,chordalDist_symm b a,chordalDist_symm (f b) (f a)] at h1 h2
  have hden : chordalDist x y * chordalDist a b ≠ 0 :=
    mul_ne_zero (chordalDist_positive hd.1).ne' (chordalDist_positive hd.2.2.2.2.2).ne'
  have hdenf : chordalDist (f x) (f y) * chordalDist (f a) (f b) ≠ 0 :=
    mul_ne_zero (chordalDist_positive (f.injective.ne hd.1)).ne'
      (chordalDist_positive (f.injective.ne hd.2.2.2.2.2)).ne'
  have he1 := (div_eq_div_iff hdenf hden).mp h1
  have he2 := (div_eq_div_iff hdenf hden).mp h2
  have he := congrArg₂ (fun u v : ℝ => u*v) he1 he2
  nlinarith only [he]

theorem distance_pair_product_bound {δ a b c : ℝ}
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδa : δ ≤ a) (hδb : δ ≤ b) (hc : c ≤ a+b) : δ*c ≤ 2*(a*b) := by
  have h1 := mul_le_mul_of_nonneg_left hc hδ
  have h2 := mul_le_mul_of_nonneg_left hδa hb
  have h3 := mul_le_mul_of_nonneg_left hδb ha
  nlinarith

theorem generalMobius_omitted_distortion_sq (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (x y a b : ExtendedEuclidean n)
    (hd : FourDistinct x y a b) (δx δy : ℝ) (hδx : 0 ≤ δx) (hδy : 0 ≤ δy)
    (hxa : δx ≤ chordalDist x a) (hxb : δx ≤ chordalDist x b)
    (hya : δy ≤ chordalDist y a) (hyb : δy ≤ chordalDist y b) :
    chordalDist (f x) (f y)^2 * chordalDist (f a) (f b)^2 * δx * δy ≤
      64 * chordalDist x y^2 := by
  have habx : chordalDist a b ≤ chordalDist x a + chordalDist x b := by
    exact (dist_triangle (stereographicHomeomorph n a) (stereographicHomeomorph n x)
      (stereographicHomeomorph n b)).trans_eq (by rw [dist_comm (stereographicHomeomorph n a)
        (stereographicHomeomorph n x)])
  have haby : chordalDist a b ≤ chordalDist y a + chordalDist y b := by
    exact (dist_triangle (stereographicHomeomorph n a) (stereographicHomeomorph n y)
      (stereographicHomeomorph n b)).trans_eq (by rw [dist_comm (stereographicHomeomorph n a)
        (stereographicHomeomorph n y)])
  have hbx := distance_pair_product_bound hδx (chordalDist_nonneg x a) (chordalDist_nonneg x b) hxa hxb habx
  have hby := distance_pair_product_bound hδy (chordalDist_nonneg y a) (chordalDist_nonneg y b) hya hyb haby
  have hpair := mul_le_mul hbx hby (mul_nonneg hδy (chordalDist_nonneg a b))
    (by positivity : 0 ≤ 2*(chordalDist x a*chordalDist x b))
  have hI : chordalDist (f x) (f a) * chordalDist (f x) (f b) *
      chordalDist (f y) (f a) * chordalDist (f y) (f b) ≤ 16 := by
    have hx := mul_le_mul (chordalDist_le_two (f x) (f a)) (chordalDist_le_two (f x) (f b))
      (chordalDist_nonneg (f x) (f b)) (by norm_num : (0:ℝ)≤2)
    have hy := mul_le_mul (chordalDist_le_two (f y) (f a)) (chordalDist_le_two (f y) (f b))
      (chordalDist_nonneg (f y) (f b)) (by norm_num : (0:ℝ)≤2)
    have hh := mul_le_mul hx hy (mul_nonneg (chordalDist_nonneg (f y) (f a)) (chordalDist_nonneg (f y) (f b))) (by
      norm_num : (0:ℝ)≤2*2)
    nlinarith only [hh]
  have hid := generalMobius_distortion_product f hf x y a b hd
  have hP : 0 < chordalDist x a * chordalDist x b * chordalDist y a * chordalDist y b := by
    exact mul_pos (mul_pos (mul_pos (chordalDist_positive hd.2.1) (chordalDist_positive hd.2.2.1))
      (chordalDist_positive hd.2.2.2.1)) (chordalDist_positive hd.2.2.2.2.1)
  have hbase := mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ chordalDist x y^2 * chordalDist a b^2)
  have hweighted := mul_le_mul_of_nonneg_left hbase (mul_nonneg hδx hδy)
  have hpair' := mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ 16 * chordalDist x y^2)
  have hfull : (chordalDist (f x) (f y)^2 * chordalDist (f a) (f b)^2 * δx * δy) *
      (chordalDist x a * chordalDist x b * chordalDist y a * chordalDist y b) ≤
      (64 * chordalDist x y^2) * (chordalDist x a * chordalDist x b * chordalDist y a * chordalDist y b) := by
    calc
      _ = (δx*δy)*(chordalDist (f x) (f y)^2 * (chordalDist x a * chordalDist x b * chordalDist y a * chordalDist
        y b) * chordalDist (f a) (f b)^2) := by ring
      _ = (δx*δy)*(chordalDist x y^2 * chordalDist a b^2 * (chordalDist (f x) (f a) * chordalDist (f x) (f b) *
        chordalDist (f y) (f a) * chordalDist (f y) (f b))) := by rw [hid]
      _ ≤ (δx*δy)*(chordalDist x y^2*chordalDist a b^2*16) := hweighted
      _ = (16*chordalDist x y^2)*((δx*chordalDist a b)*(δy*chordalDist a b)) := by ring
      _ ≤ (16*chordalDist x y^2)*((2*(chordalDist x a*chordalDist x b))*(2*(chordalDist y a*chordalDist y b))) := hpair'
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ hP).mp hfull

theorem generalMobius_omitted_distortion (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (x y a b : ExtendedEuclidean n)
    (hd : FourDistinct x y a b) (δx δy : ℝ) (hδx : 0 < δx) (hδy : 0 < δy)
    (hxa : δx ≤ chordalDist x a) (hxb : δx ≤ chordalDist x b)
    (hya : δy ≤ chordalDist y a) (hyb : δy ≤ chordalDist y b) :
    chordalDist (f x) (f y) ≤ 8 * chordalDist x y /
      (chordalDist (f a) (f b) * Real.sqrt δx * Real.sqrt δy) := by
  have hs := generalMobius_omitted_distortion_sq f hf x y a b hd δx δy hδx.le hδy.le hxa hxb hya hyb
  have hroot : (chordalDist (f x) (f y) * chordalDist (f a) (f b) * Real.sqrt δx * Real.sqrt δy)^2 ≤ (8 *
    chordalDist x y)^2 := by
    calc
      _ = chordalDist (f x) (f y)^2 * chordalDist (f a) (f b)^2 * δx * δy := by
        simp only [mul_pow,Real.sq_sqrt hδx.le,Real.sq_sqrt hδy.le]
      _ ≤ 64 * chordalDist x y^2 := hs
      _ = _ := by ring
  have hlinear : chordalDist (f x) (f y) * chordalDist (f a) (f b) * Real.sqrt δx * Real.sqrt δy ≤ 8 * chordalDist
    x y :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hroot
  have hden : 0 < chordalDist (f a) (f b) * Real.sqrt δx * Real.sqrt δy :=
    mul_pos (mul_pos (chordalDist_positive (f.injective.ne hd.2.2.2.2.2))
      (Real.sqrt_pos.mpr hδx)) (Real.sqrt_pos.mpr hδy)
  exact (le_div_iff₀ hden).mpr (by simpa only [mul_assoc] using hlinear)

section Domain
local instance distortionDomainChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n

theorem generalMobius_omitted_distortion_compl (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (D : Set (ExtendedEuclidean n)) (hD : IsOpen D)
    (a b : ExtendedEuclidean n) (hab : a ≠ b) (ha : a ∉ f '' D) (hb : b ∉ f '' D)
    (x y : ExtendedEuclidean n) (hx : x ∈ D) (hy : y ∈ D) :
    chordalDist (f x) (f y) ≤ 8 * chordalDist x y /
      (chordalDist a b * Real.sqrt (Metric.infDist x Dᶜ) * Real.sqrt (Metric.infDist y Dᶜ)) := by
  have ha' : f.symm a ∈ Dᶜ := by
    intro h
    exact ha ⟨f.symm a,h,f.apply_symm_apply a⟩
  have hb' : f.symm b ∈ Dᶜ := by
    intro h
    exact hb ⟨f.symm b,h,f.apply_symm_apply b⟩
  have hδx : 0 < Metric.infDist x Dᶜ := (hD.isClosed_compl.notMem_iff_infDist_pos ⟨f.symm a,ha'⟩).mp (by simpa using hx)
  have hδy : 0 < Metric.infDist y Dᶜ := (hD.isClosed_compl.notMem_iff_infDist_pos ⟨f.symm a,ha'⟩).mp (by simpa using hy)
  by_cases hxy : x=y
  · subst y
    simp [chordalDist]
  have hd : FourDistinct x y (f.symm a) (f.symm b) := by
    refine ⟨hxy,?_,?_,?_,?_,f.symm.injective.ne hab⟩
    · intro he; exact ha' (he ▸ hx)
    · intro he; exact hb' (he ▸ hx)
    · intro he; exact ha' (he ▸ hy)
    · intro he; exact hb' (he ▸ hy)
  have hh := generalMobius_omitted_distortion f hf x y (f.symm a) (f.symm b) hd
    (Metric.infDist x Dᶜ) (Metric.infDist y Dᶜ) hδx hδy
    (Metric.infDist_le_dist_of_mem ha') (Metric.infDist_le_dist_of_mem hb')
    (Metric.infDist_le_dist_of_mem ha') (Metric.infDist_le_dist_of_mem hb')
  simpa only [f.apply_symm_apply] using hh

theorem generalMobius_omitted_distortion_uniform (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (D : Set (ExtendedEuclidean n)) (hD : IsOpen D)
    (a b : ExtendedEuclidean n) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (ha : a ∉ f '' D) (hb : b ∉ f '' D) (hab : ε ≤ chordalDist a b)
    (x y : ExtendedEuclidean n) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : r ≤ Metric.infDist x Dᶜ) (hry : r ≤ Metric.infDist y Dᶜ) :
    chordalDist (f x) (f y) ≤ (8/(ε*r)) * chordalDist x y := by
  have hsep : 0 < chordalDist a b := hε.trans_le hab
  have hab' : a ≠ b := by intro h; simp [h,chordalDist] at hsep
  have hh := generalMobius_omitted_distortion_compl f hf D hD a b hab' ha hb x y hx hy
  have hprod : ε*r ≤ chordalDist a b * Real.sqrt (Metric.infDist x Dᶜ) * Real.sqrt (Metric.infDist y Dᶜ) := by
    have hxr := Real.sqrt_le_sqrt hrx
    have hyr := Real.sqrt_le_sqrt hry
    have hroot := mul_le_mul hxr hyr (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hr.le] at hroot
    calc
      ε*r ≤ chordalDist a b*r := mul_le_mul_of_nonneg_right hab hr.le
      _ ≤ chordalDist a b*(Real.sqrt (Metric.infDist x Dᶜ)*Real.sqrt (Metric.infDist y Dᶜ)) :=
        mul_le_mul_of_nonneg_left hroot hsep.le
      _ = _ := by ring
  calc
    _ ≤ 8 * chordalDist x y / (chordalDist a b * Real.sqrt (Metric.infDist x Dᶜ) * Real.sqrt (Metric.infDist y
      Dᶜ)) := hh
    _ ≤ 8 * chordalDist x y / (ε*r) := div_le_div_of_nonneg_left (by positivity) (mul_pos hε hr) hprod
    _ = _ := by ring

end Domain

def unitSphereLinearHomeomorph (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) :
    Metric.sphere (0 : Euclidean (n+1)) 1 ≃ₜ Metric.sphere (0 : Euclidean (n+1)) 1 :=
  (L.toHomeomorph.image (Metric.sphere (0 : Euclidean (n+1)) 1)).trans
    (Homeomorph.setCongr (by simpa only [LinearIsometryEquiv.coe_toHomeomorph,L.map_zero] using L.image_sphere 0 1))

def chordalOrthogonalHomeomorph (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) : ExtendedHomeomorph n :=
  (stereographicHomeomorph n).trans ((unitSphereLinearHomeomorph L).trans (stereographicHomeomorph n).symm)

theorem chordalOrthogonalHomeomorph_stereographic
    (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (x : ExtendedEuclidean n) :
    ((stereographicHomeomorph n (chordalOrthogonalHomeomorph L x)).val) =
      L (stereographicHomeomorph n x).val := by
  change ((stereographicHomeomorph n) ((stereographicHomeomorph n).symm _)).val = _
  rw [(stereographicHomeomorph n).apply_symm_apply]
  rfl

theorem chordalOrthogonalHomeomorph_dist
    (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (x y : ExtendedEuclidean n) :
    chordalDist (chordalOrthogonalHomeomorph L x) (chordalOrthogonalHomeomorph L y) = chordalDist x y := by
  change dist ((stereographicHomeomorph n (chordalOrthogonalHomeomorph L x)).val)
    ((stereographicHomeomorph n (chordalOrthogonalHomeomorph L y)).val) = _
  rw [chordalOrthogonalHomeomorph_stereographic,chordalOrthogonalHomeomorph_stereographic]
  exact L.isometry.dist_eq _ _

theorem exists_chordal_centering (x : ExtendedEuclidean n) : ∃ h : ExtendedHomeomorph n,
    h x = (0 : Euclidean n) ∧ ∀ y z, chordalDist (h y) (h z) = chordalDist y z := by
  let p := (stereographicHomeomorph n x).val
  let q := -northPole n
  let L := cartanPlaneLinearIsometry (p-q)
  have hp : ‖p‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using (stereographicHomeomorph n x).property
  have hq : ‖q‖ = 1 := by simp [q,norm_northPole]
  have hLp : L p = q := Submodule.reflection_sub (hp.trans hq.symm)
  refine ⟨chordalOrthogonalHomeomorph L,?_,chordalOrthogonalHomeomorph_dist L⟩
  apply (stereographicHomeomorph n).injective
  apply Subtype.ext
  rw [chordalOrthogonalHomeomorph_stereographic]
  change L p = _
  rw [hLp]
  simp [q,stereographicHomeomorph_coe]

theorem chordalDist_zero_coe_sq (x : Euclidean n) :
    chordalDist (0 : Euclidean n) (x : ExtendedEuclidean n)^2 = 4*‖x‖^2/(1+‖x‖^2) := by
  rw [chordalDist_coe_coe]
  simp only [norm_zero,dist_zero_left,div_pow,mul_pow,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1+‖x‖^2)]
  ring

theorem chordalDist_zero_coe_mono {x y : Euclidean n} (h : ‖x‖ ≤ ‖y‖) :
    chordalDist (0 : Euclidean n) (x : ExtendedEuclidean n) ≤ chordalDist (0 : Euclidean n) (y : ExtendedEuclidean
      n) := by
  apply (sq_le_sq₀ (chordalDist_nonneg _ _) (chordalDist_nonneg _ _)).mp
  rw [chordalDist_zero_coe_sq,chordalDist_zero_coe_sq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
  nlinarith

theorem chordalDist_zero_smul_le (x : Euclidean n) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    chordalDist (0 : Euclidean n) ((t • x : Euclidean n) : ExtendedEuclidean n) ≤ chordalDist (0 : Euclidean n) (x
      : ExtendedEuclidean n) := by
  apply chordalDist_zero_coe_mono
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

theorem preconnected_meets_frontier {X : Type*} [TopologicalSpace X] {S D : Set X}
    (hS : IsPreconnected S) (hD : IsOpen D) {x y : X} (hxS : x ∈ S) (hyS : y ∈ S)
    (hxD : x ∈ D) (hyD : y ∉ D) : (S ∩ frontier D).Nonempty := by
  by_contra h
  have hsub : closure D ∩ S ⊆ D := by
    rintro z ⟨hzD,hzS⟩
    by_contra hz
    apply h
    exact ⟨z,hzS,by rw [frontier,hD.interior_eq]; exact ⟨hzD,hz⟩⟩
  exact hyD (hS.subset_of_closure_inter_subset hD ⟨x,hxS,hxD⟩ hsub hyS)

section Frontier
local instance distortionFrontierChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n

theorem chordal_infDist_frontier_le [NeZero n] (D : Set (ExtendedEuclidean n)) (hD : IsOpen D)
    (x : ExtendedEuclidean n) (hx : x ∈ D) (a : ExtendedEuclidean n) (ha : a ∉ D) :
    Metric.infDist x (frontier D) ≤ chordalDist x a := by
  obtain ⟨h,hx0,hq⟩ := exists_chordal_centering x
  by_cases hi : h a = ∞
  · obtain ⟨z,hz⟩ := (nonempty_frontier_iff (s := D)).mpr ⟨⟨x,hx⟩,by intro he; simp [he] at ha⟩
    have hxa : chordalDist x a = 2 := by
      rw [← hq x a,hx0,hi,chordalDist_coe_infty]
      norm_num
    rw [hxa]
    exact (Metric.infDist_le_dist_of_mem hz).trans (chordalDist_le_two x z)
  obtain ⟨b,hb⟩ := OnePoint.ne_infty_iff_exists.mp hi
  let γ : ℝ → ExtendedEuclidean n := fun t => h.symm ((t • b : Euclidean n) : ExtendedEuclidean n)
  have hγ : Continuous γ := h.symm.continuous.comp
    (OnePoint.continuous_coe.comp (continuous_id.smul continuous_const))
  have hzero : γ 0 = x := by
    apply h.injective
    change h (h.symm _) = h x
    rw [h.apply_symm_apply,hx0,zero_smul]
  have hone : γ 1 = a := by
    change h.symm ((1 • b : Euclidean n) : ExtendedEuclidean n) = a
    rw [one_smul,hb,h.symm_apply_apply]
  have hS : IsPreconnected (γ '' Icc (0:ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  obtain ⟨z,⟨t,ht,rfl⟩,hz⟩ := preconnected_meets_frontier hS hD
    ⟨0,by norm_num,hzero⟩ ⟨1,by norm_num,hone⟩ hx ha
  calc
    Metric.infDist x (frontier D) ≤ chordalDist x (γ t) := Metric.infDist_le_dist_of_mem hz
    _ = chordalDist (0 : Euclidean n) ((t • b : Euclidean n) : ExtendedEuclidean n) := by
      rw [← hq x (γ t),hx0]
      congr 1
      exact h.apply_symm_apply _
    _ ≤ chordalDist (0 : Euclidean n) (b : ExtendedEuclidean n) := chordalDist_zero_smul_le b ht
    _ = chordalDist x a := by rw [← hq x a,hx0,← hb]

theorem chordal_infDist_frontier_eq_compl [NeZero n] (D : Set (ExtendedEuclidean n))
    (hD : IsOpen D) (hDc : Dᶜ.Nonempty) (x : ExtendedEuclidean n) (hx : x ∈ D) :
    Metric.infDist x (frontier D) = Metric.infDist x Dᶜ := by
  apply le_antisymm
  · exact (Metric.le_infDist hDc).mpr (fun _ ha => chordal_infDist_frontier_le D hD x hx _ ha)
  · apply Metric.infDist_le_infDist_of_subset
    · intro z hz
      rw [hD.frontier_eq] at hz
      exact hz.2
    · exact nonempty_frontier_iff.mpr ⟨⟨x,hx⟩,by intro he; simp [he] at hDc⟩

theorem generalMobius_omitted_distortion_frontier [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (D : Set (ExtendedEuclidean n)) (hD : IsOpen D)
    (a b : ExtendedEuclidean n) (hab : a ≠ b) (ha : a ∉ f '' D) (hb : b ∉ f '' D)
    (x y : ExtendedEuclidean n) (hx : x ∈ D) (hy : y ∈ D) :
    chordalDist (f x) (f y) ≤ 8 * chordalDist x y /
      (chordalDist a b * Real.sqrt (Metric.infDist x (frontier D)) * Real.sqrt (Metric.infDist y (frontier D))) := by
  have hDc : Dᶜ.Nonempty := ⟨f.symm a,by
    intro h
    exact ha ⟨f.symm a,h,f.apply_symm_apply a⟩⟩
  rw [chordal_infDist_frontier_eq_compl D hD hDc x hx,chordal_infDist_frontier_eq_compl D hD hDc y hy]
  exact generalMobius_omitted_distortion_compl f hf D hD a b hab ha hb x y hx hy

end Frontier

theorem ballBoundaryAction_stereographic (f : ExtendedHomeomorph (n+1)) (hB : PreservesUnitBall f)
    (x : ExtendedEuclidean n) :
    (stereographicHomeomorph n (Hyperbolic.ballBoundaryAction f hB x)).val =
      finiteEuclideanPart f (stereographicHomeomorph n x).val := by
  have hh := Hyperbolic.ballBoundaryAction_transport f hB x
  rw [Hyperbolic.cayleyBall_equatorial,Hyperbolic.cayleyBall_equatorial] at hh
  apply OnePoint.coe_injective
  exact hh.trans (coe_finiteEuclideanPart f (hB.norm_on_sphere _
    (by simpa only [Metric.mem_sphere,dist_zero_right] using (stereographicHomeomorph n x).property)).1).symm

theorem ballBoundaryAction_dist (f : ExtendedHomeomorph (n+1)) (hB : PreservesUnitBall f)
    (x y : ExtendedEuclidean n) :
    chordalDist (Hyperbolic.ballBoundaryAction f hB x) (Hyperbolic.ballBoundaryAction f hB y) =
      dist (finiteEuclideanPart f (stereographicHomeomorph n x).val)
        (finiteEuclideanPart f (stereographicHomeomorph n y).val) := by
  change dist (stereographicHomeomorph n (Hyperbolic.ballBoundaryAction f hB x)).val
    (stereographicHomeomorph n (Hyperbolic.ballBoundaryAction f hB y)).val = _
  rw [ballBoundaryAction_stereographic,ballBoundaryAction_stereographic]

theorem ballBoundaryAction_linear_dist (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1))
    (hB : PreservesUnitBall (cartanLinearExtensionHom L)) (x y : ExtendedEuclidean n) :
    chordalDist (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L) hB x)
      (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L) hB y) = chordalDist x y := by
  rw [ballBoundaryAction_dist]
  change dist (L (stereographicHomeomorph n x).val) (L (stereographicHomeomorph n y).val) = _
  exact L.isometry.dist_eq _ _

theorem unitSphere_ne_exterior_center {c x : Euclidean (n+1)} (hc : 1 < ‖c‖) (hx : ‖x‖ = 1) : x ≠ c := by
  intro he
  rw [he] at hx
  linarith

theorem unitSphere_dist_exterior_lower {c x : Euclidean (n+1)} (hx : ‖x‖ = 1) : ‖c‖-1 ≤ dist x c := by
  have h := norm_sub_norm_le c x
  rw [hx,← dist_eq_norm,dist_comm] at h
  exact h

theorem ballBoundaryAction_sphere_dist
    (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (c : Euclidean (n+1)) (r : ℝ)
    (hr : 0 < r) (hc : 1 < ‖c‖)
    (hB : PreservesUnitBall (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne'))
    (x y : ExtendedEuclidean n) :
    chordalDist (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB x)
      (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB y) =
      r^2/(dist (stereographicHomeomorph n x).val c * dist (stereographicHomeomorph n y).val c) * chordalDist x y := by
  have hreg (z : ExtendedEuclidean n) : (stereographicHomeomorph n z).val ≠ c :=
    unitSphere_ne_exterior_center hc (by simpa only [Metric.mem_sphere,dist_zero_right] using
      (stereographicHomeomorph n z).property)
  have hval (z : ExtendedEuclidean n) :
      finiteEuclideanPart (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne')
        (stereographicHomeomorph n z).val =
        L (inversion c r (stereographicHomeomorph n z).val) := by
    unfold finiteEuclideanPart
    change (cartanLinearExtensionHom L (sphereInversion c r (stereographicHomeomorph n z).val)).elim 0 id = _
    rw [sphereInversion_coe c r (hreg z),cartanLinearExtensionHom_coe]
    rfl
  rw [ballBoundaryAction_dist,hval x,hval y,L.isometry.dist_eq]
  exact sphereInversion_dist r (hreg x) (hreg y)

theorem orthogonalSphere_boundary_scale (c : Euclidean (n+1)) (r : ℝ)
    (horth : ‖c‖^2 = 1+r^2) (hc : 1 < ‖c‖) :
    r^2/(‖c‖-1)^2 = (‖c‖+1)/(‖c‖-1) := by
  apply (div_eq_div_iff (pow_ne_zero 2 (by linarith : ‖c‖-1 ≠ 0)) (by linarith : ‖c‖-1 ≠ 0)).mpr
  nlinarith

theorem ballBoundaryAction_sphere_lipschitz
    (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (c : Euclidean (n+1)) (r : ℝ)
    (hr : 0 < r) (hc : 1 < ‖c‖) (horth : ‖c‖^2 = 1+r^2)
    (hB : PreservesUnitBall (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne'))
    (x y : ExtendedEuclidean n) :
    chordalDist (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB x)
      (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB y) ≤
      ((‖c‖+1)/(‖c‖-1)) * chordalDist x y := by
  have hdist (z : ExtendedEuclidean n) : ‖c‖-1 ≤ dist (stereographicHomeomorph n z).val c :=
    unitSphere_dist_exterior_lower (by simpa only [Metric.mem_sphere,dist_zero_right] using
      (stereographicHomeomorph n z).property)
  have hpos : 0 < ‖c‖-1 := sub_pos.mpr hc
  have hp := mul_le_mul (hdist x) (hdist y) hpos.le ((hpos.trans_le (hdist x)).le)
  rw [← pow_two] at hp
  rw [ballBoundaryAction_sphere_dist L c r hr hc hB]
  apply mul_le_mul_of_nonneg_right _ (chordalDist_nonneg x y)
  rw [← orthogonalSphere_boundary_scale c r horth hc]
  exact div_le_div_of_nonneg_left (sq_nonneg r) (sq_pos_of_pos hpos) hp

def nearestUnitPoint (c : Euclidean (n+1)) : Euclidean (n+1) := ‖c‖⁻¹ • c

theorem nearestUnitPoint_norm (c : Euclidean (n+1)) (hc : 1 < ‖c‖) : ‖nearestUnitPoint c‖ = 1 := by
  have ha : 0 < ‖c‖ := zero_lt_one.trans hc
  rw [nearestUnitPoint,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),inv_mul_cancel₀ ha.ne']

theorem nearestUnitPoint_dist (c : Euclidean (n+1)) (hc : 1 < ‖c‖) : dist (nearestUnitPoint c) c = ‖c‖-1 := by
  have ha : 0 < ‖c‖ := zero_lt_one.trans hc
  have hi : ‖c‖⁻¹ ≤ 1 := (inv_le_one₀ ha).mpr hc.le
  have he : nearestUnitPoint c-c = (‖c‖⁻¹-1) • c := by unfold nearestUnitPoint; module
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hi)]
  field_simp [ha.ne']
  ring

def nearestUnitBoundary (c : Euclidean (n+1)) (hc : 1 < ‖c‖) : ExtendedEuclidean n :=
  (stereographicHomeomorph n).symm ⟨nearestUnitPoint c,by rw
    [Metric.mem_sphere,dist_zero_right,nearestUnitPoint_norm c hc]⟩

theorem stereographic_nearestUnitBoundary (c : Euclidean (n+1)) (hc : 1 < ‖c‖) :
    (stereographicHomeomorph n (nearestUnitBoundary c hc)).val = nearestUnitPoint c := by
  exact congrArg Subtype.val ((stereographicHomeomorph n).apply_symm_apply _)

theorem ballBoundaryAction_sphere_ratio_limit [NeZero n]
    (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (c : Euclidean (n+1)) (r : ℝ)
    (hr : 0 < r) (hc : 1 < ‖c‖) (horth : ‖c‖^2 = 1+r^2)
    (hB : PreservesUnitBall (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne')) :
    Tendsto (fun y => chordalDist
      (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB
        (nearestUnitBoundary c hc))
      (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB y) /
      chordalDist (nearestUnitBoundary c hc) y)
      (𝓝[≠] (nearestUnitBoundary c hc)) (𝓝 ((‖c‖+1)/(‖c‖-1))) := by
  let p := nearestUnitBoundary c hc
  have hdp : dist (stereographicHomeomorph n p).val c = ‖c‖-1 := by
    rw [stereographic_nearestUnitBoundary,nearestUnitPoint_dist c hc]
  have hpos : 0 < ‖c‖-1 := sub_pos.mpr hc
  have hcont : ContinuousAt (fun y : ExtendedEuclidean n =>
      r^2/(dist (stereographicHomeomorph n p).val c * dist (stereographicHomeomorph n y).val c)) p := by
    apply continuousAt_const.div
      (continuousAt_const.mul (((continuous_subtype_val.comp (stereographicHomeomorph
        n).continuous).continuousAt).dist continuousAt_const))
    change dist (stereographicHomeomorph n p).val c * dist (stereographicHomeomorph n p).val c ≠ 0
    rw [hdp]
    exact mul_ne_zero hpos.ne' hpos.ne'
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] p ≤ 𝓝 p)
  change Tendsto _ _ (𝓝 (r^2/(dist (stereographicHomeomorph n p).val c * dist (stereographicHomeomorph n p).val
    c))) at hlim
  rw [hdp,← pow_two,orthogonalSphere_boundary_scale c r horth hc] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hpy : p ≠ y := Ne.symm hy
  rw [ballBoundaryAction_sphere_dist L c r hr hc hB]
  change r^2/((‖c‖-1)*dist (stereographicHomeomorph n y).val c) =
    r^2/(dist (stereographicHomeomorph n p).val c * dist (stereographicHomeomorph n y).val c) * chordalDist p y /
      chordalDist p y
  rw [hdp]
  exact (mul_div_cancel_right₀ _ (chordalDist_positive hpy).ne').symm

theorem ballBoundaryAction_sphere_least_lipschitz [NeZero n]
    (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (c : Euclidean (n+1)) (r : ℝ)
    (hr : 0 < r) (hc : 1 < ‖c‖) (horth : ‖c‖^2 = 1+r^2)
    (hB : PreservesUnitBall (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne')) :
    IsLeast {K : ℝ | ∀ x y : ExtendedEuclidean n,
      chordalDist (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r
        hr.ne') hB x)
        (Hyperbolic.ballBoundaryAction (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB y) ≤
          K * chordalDist x y}
      ((‖c‖+1)/(‖c‖-1)) := by
  refine ⟨ballBoundaryAction_sphere_lipschitz L c r hr hc horth hB,?_⟩
  intro K hK
  apply le_of_tendsto (ballBoundaryAction_sphere_ratio_limit L c r hr hc horth hB)
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hpy : nearestUnitBoundary c hc ≠ y := Ne.symm hy
  exact (div_le_iff₀ (chordalDist_positive hpy)).mpr (hK _ y)

theorem ballHomeomorph_sphere_origin_norm
    (L : Euclidean (n+1) ≃ₗᵢ[ℝ] Euclidean (n+1)) (c : Euclidean (n+1)) (r : ℝ)
    (hr : 0 < r) (hc : 1 < ‖c‖) (horth : ‖c‖^2 = 1+r^2)
    (hB : PreservesUnitBall (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne')) :
    ‖(Hyperbolic.ballHomeomorph (cartanLinearExtensionHom L * sphereInversionHomeomorph c r hr.ne') hB
      (Hyperbolic.ballOrigin (n+1))).val‖ = ‖c‖⁻¹ := by
  have hc0 : c ≠ 0 := by intro h; rw [h,norm_zero] at hc; linarith
  rw [Hyperbolic.ballHomeomorph_val,finiteEuclideanPart_linear_mul,L.norm_map]
  change ‖(sphereInversion c r (0 : Euclidean (n+1))).elim 0 id‖ = _
  rw [sphereInversion_coe c r (Ne.symm hc0),boundaryOrthogonal_inversion_zero c r hc0 horth]
  exact norm_unitInversion c

theorem ballBoundaryAction_least_lipschitz [NeZero n]
    (f : ExtendedHomeomorph (n+1)) (hf : f ∈ generalMobiusGroup (n+1)) (hB : PreservesUnitBall f) :
    IsLeast {K : ℝ | ∀ x y : ExtendedEuclidean n,
      chordalDist (Hyperbolic.ballBoundaryAction f hB x) (Hyperbolic.ballBoundaryAction f hB y) ≤ K * chordalDist x y}
      (Real.exp ((Hyperbolic.ballDensity (n+1)).pathDist (Hyperbolic.ballOrigin (n+1)) (Hyperbolic.ballHomeomorph
        f hB (Hyperbolic.ballOrigin (n+1))))) := by
  by_cases hi : f ∞ = ∞
  · obtain ⟨L,rfl⟩ := ball_preserving_fix_zero_linearIsometry f hf hB (generalMobius_ball_fixing_infty_fixes_zero
      f hf hB hi)
    have hzero : Hyperbolic.ballHomeomorph (cartanLinearExtensionHom L) hB (Hyperbolic.ballOrigin (n+1)) =
      Hyperbolic.ballOrigin (n+1) := by
      apply Subtype.ext
      rw [Hyperbolic.ballHomeomorph_val]
      change L 0 = 0
      exact L.map_zero
    rw [hzero,Auxiliary.Analysis.Density.pathDist_self,Real.exp_zero]
    refine ⟨?_,?_⟩
    · intro x y
      rw [ballBoundaryAction_linear_dist,one_mul]
    · intro K hK
      have hh := hK ∞ (0 : Euclidean n)
      rw [ballBoundaryAction_linear_dist,chordalDist_infty_coe] at hh
      norm_num at hh
      linarith
  · obtain ⟨c,r,hr,horth,L,rfl⟩ := generalMobius_ball_nonAffine_orthogonal_reflection f hf hB hi
    have hc : 1 < ‖c‖ := by nlinarith [norm_nonneg c,sq_pos_of_pos hr]
    have ha : 0 < ‖c‖ := zero_lt_one.trans hc
    rw [Hyperbolic.ballDensity_pathDist_origin,ballHomeomorph_sphere_origin_norm L c r hr hc horth]
    have hi0 : 0 < 1-‖c‖⁻¹ := by
      exact sub_pos.mpr ((inv_lt_one₀ ha).mpr hc)
    have hp : 0 < (1+‖c‖⁻¹)/(1-‖c‖⁻¹) := div_pos (by positivity) hi0
    rw [Real.exp_log hp]
    have he : (1+‖c‖⁻¹)/(1-‖c‖⁻¹) = (‖c‖+1)/(‖c‖-1) := by
      field_simp [ha.ne']
    rw [he]
    exact ballBoundaryAction_sphere_least_lipschitz L c r hr hc horth hB

theorem ballBoundaryAction_cayley_poincare [NeZero n] (g : GM n) :
    Hyperbolic.ballBoundaryAction (Hyperbolic.cayleyBall n * (Hyperbolic.poincareExtension g : ExtendedHomeomorph
      (n+1)) * (Hyperbolic.cayleyBall n)⁻¹)
      (Hyperbolic.cayleyBall_poincare_conjugate_preservesUnitBall g) = (g : ExtendedHomeomorph n) := by
  ext z
  apply extendedEquatorialEmbedding_injective n
  apply (Hyperbolic.cayleyBall n).injective
  rw [Hyperbolic.ballBoundaryAction_transport]
  change Hyperbolic.cayleyBall n ((Hyperbolic.poincareExtension g : ExtendedHomeomorph (n+1))
    ((Hyperbolic.cayleyBall n).symm (Hyperbolic.cayleyBall n (extendedEquatorialEmbedding n z)))) = _
  rw [(Hyperbolic.cayleyBall n).symm_apply_apply,Hyperbolic.poincareExtension_extendsBoundary]

theorem cayleyPoincare_ballHomeomorph [NeZero n] (g : GM n) (x : Hyperbolic.HyperbolicHalfSpace n) :
    Hyperbolic.ballHomeomorph (Hyperbolic.cayleyBall n * (Hyperbolic.poincareExtension g : ExtendedHomeomorph
      (n+1)) * (Hyperbolic.cayleyBall n)⁻¹)
      (Hyperbolic.cayleyBall_poincare_conjugate_preservesUnitBall g) (Hyperbolic.cayleyBallHomeomorph n x) =
      Hyperbolic.cayleyBallHomeomorph n (Hyperbolic.poincareHalfSpaceHomeomorph g x) := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  rw [Hyperbolic.ballHomeomorph_coe, Hyperbolic.cayleyBallHomeomorph_coe,
    Hyperbolic.cayleyBallHomeomorph_coe, Hyperbolic.poincareHalfSpaceHomeomorph_apply]
  change Hyperbolic.cayleyBall n ((Hyperbolic.poincareExtension g : ExtendedHomeomorph (n+1))
    ((Hyperbolic.cayleyBall n).symm (Hyperbolic.cayleyBall n x.val))) = _
  rw [(Hyperbolic.cayleyBall n).symm_apply_apply]

theorem cayleyBallHomeomorph_vertical_one (n : ℕ) :
    Hyperbolic.cayleyBallHomeomorph n (Hyperbolic.verticalPoint n 1 zero_lt_one) = Hyperbolic.ballOrigin (n+1) := by
  apply Subtype.ext
  rw [Hyperbolic.cayleyBallHomeomorph_vertical]
  simp [Hyperbolic.ballOrigin]

theorem cayleyPoincare_origin_displacement [NeZero n] (g : GM n) :
    (Hyperbolic.ballDensity (n+1)).pathDist (Hyperbolic.ballOrigin (n+1))
      (Hyperbolic.ballHomeomorph (Hyperbolic.cayleyBall n * (Hyperbolic.poincareExtension g : ExtendedHomeomorph
        (n+1)) * (Hyperbolic.cayleyBall n)⁻¹)
        (Hyperbolic.cayleyBall_poincare_conjugate_preservesUnitBall g) (Hyperbolic.ballOrigin (n+1))) =
      Hyperbolic.halfSpacePathDist (Hyperbolic.verticalPoint n 1 zero_lt_one)
        (Hyperbolic.poincareHalfSpaceHomeomorph g (Hyperbolic.verticalPoint n 1 zero_lt_one)) := by
  rw [← cayleyBallHomeomorph_vertical_one n,cayleyPoincare_ballHomeomorph,Hyperbolic.cayleyBallHomeomorph_pathDist]

theorem generalMobius_least_chordal_lipschitz [NeZero n] (g : GM n) :
    IsLeast {K : ℝ | ∀ x y : ExtendedEuclidean n,
      chordalDist ((g : ExtendedHomeomorph n) x) ((g : ExtendedHomeomorph n) y) ≤ K * chordalDist x y}
      (Real.exp (Hyperbolic.halfSpacePathDist (Hyperbolic.verticalPoint n 1 zero_lt_one)
        (Hyperbolic.poincareHalfSpaceHomeomorph g (Hyperbolic.verticalPoint n 1 zero_lt_one)))) := by
  let F : ExtendedHomeomorph (n+1) := Hyperbolic.cayleyBall n * (Hyperbolic.poincareExtension g :
    ExtendedHomeomorph (n+1)) * (Hyperbolic.cayleyBall n)⁻¹
  have hF : F ∈ generalMobiusGroup (n+1) :=
    (generalMobiusGroup (n+1)).mul_mem ((generalMobiusGroup (n+1)).mul_mem
      (Hyperbolic.cayleyBall_mem_generalMobiusGroup n) (Hyperbolic.poincareExtension g).property)
      ((generalMobiusGroup (n+1)).inv_mem (Hyperbolic.cayleyBall_mem_generalMobiusGroup n))
  have hh := ballBoundaryAction_least_lipschitz F hF (Hyperbolic.cayleyBall_poincare_conjugate_preservesUnitBall g)
  rw [ballBoundaryAction_cayley_poincare,cayleyPoincare_origin_displacement] at hh
  exact hh

theorem generalMobius_chordal_distortion_isLUB [NeZero n] (g : GM n) :
    IsLUB {r : ℝ | ∃ x y : ExtendedEuclidean n, x ≠ y ∧
      r = chordalDist ((g : ExtendedHomeomorph n) x) ((g : ExtendedHomeomorph n) y) / chordalDist x y}
      (Real.exp (Hyperbolic.halfSpacePathDist (Hyperbolic.verticalPoint n 1 zero_lt_one)
        (Hyperbolic.poincareHalfSpaceHomeomorph g (Hyperbolic.verticalPoint n 1 zero_lt_one)))) := by
  have hh := generalMobius_least_chordal_lipschitz g
  refine ⟨?_,?_⟩
  · rintro r ⟨x,y,hxy,rfl⟩
    exact (div_le_iff₀ (chordalDist_positive hxy)).mpr (hh.1 x y)
  · intro K hK
    apply hh.2
    intro x y
    by_cases hxy : x=y
    · simp [hxy,chordalDist]
    · exact (div_le_iff₀ (chordalDist_positive hxy)).mp (hK ⟨x,y,hxy,rfl⟩)

/-- For the genuine Poincaré extension and path metric. -/
theorem chordal_distortion_sup_eq_exp_origin_displacement [NeZero n] (g : GM n) :
    sSup {r : ℝ | ∃ x y : ExtendedEuclidean n, x ≠ y ∧
      r = chordalDist ((g : ExtendedHomeomorph n) x) ((g : ExtendedHomeomorph n) y) / chordalDist x y} =
      Real.exp (Hyperbolic.halfSpacePathDist (Hyperbolic.verticalPoint n 1 zero_lt_one)
        (Hyperbolic.poincareHalfSpaceHomeomorph g (Hyperbolic.verticalPoint n 1 zero_lt_one))) :=
  (generalMobius_chordal_distortion_isLUB g).csSup_eq
    ⟨_,∞,(0 : Euclidean n),OnePoint.infty_ne_coe 0,rfl⟩

theorem chordal_translation_ratio (v x y : Euclidean n) (hxy : x ≠ y) :
    chordalDist (translationHomeomorph v x) (translationHomeomorph v y) /
      chordalDist (x : ExtendedEuclidean n) (y : ExtendedEuclidean n) =
    (Real.sqrt (1+‖x‖^2)*Real.sqrt (1+‖y‖^2)) /
      (Real.sqrt (1+‖x+v‖^2)*Real.sqrt (1+‖y+v‖^2)) := by
  rw [translationHomeomorph_coe,translationHomeomorph_coe,chordalDist_coe_coe,chordalDist_coe_coe,dist_add_right]
  have hx : Real.sqrt (1+‖x‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hy : Real.sqrt (1+‖y‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hvx : Real.sqrt (1+‖x+v‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hvy : Real.sqrt (1+‖y+v‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hx,hy,hvx,hvy,dist_ne_zero.mpr hxy]

theorem chordal_translation_ratio_limit (v x : Euclidean n) :
    Tendsto (fun y : Euclidean n => chordalDist (translationHomeomorph v x) (translationHomeomorph v y) /
      chordalDist (x : ExtendedEuclidean n) (y : ExtendedEuclidean n)) (𝓝[≠] x)
      (𝓝 ((1+‖x‖^2)/(1+‖x+v‖^2))) := by
  have hcont : ContinuousAt (fun y : Euclidean n =>
      (Real.sqrt (1+‖x‖^2)*Real.sqrt (1+‖y‖^2)) /
        (Real.sqrt (1+‖x+v‖^2)*Real.sqrt (1+‖y+v‖^2))) x := by
    apply (continuousAt_const.mul ((continuousAt_const.add (continuousAt_id.norm.pow 2)).sqrt)).div
      (continuousAt_const.mul ((continuousAt_const.add ((continuousAt_id.add continuousAt_const).norm.pow 2)).sqrt))
    change Real.sqrt (1+‖x+v‖^2)*Real.sqrt (1+‖x+v‖^2) ≠ 0
    exact mul_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne' (Real.sqrt_pos.mpr (by positivity)).ne'
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] x ≤ 𝓝 x)
  change Tendsto _ _ (𝓝 ((Real.sqrt (1+‖x‖^2)*Real.sqrt (1+‖x‖^2)) /
    (Real.sqrt (1+‖x+v‖^2)*Real.sqrt (1+‖x+v‖^2)))) at hlim
  rw [Real.mul_self_sqrt (by positivity),Real.mul_self_sqrt (by positivity)] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (chordal_translation_ratio v x y (Ne.symm hy)).symm

section Sharp
local instance distortionSharpChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n

theorem metric_infDist_pair (x a b : ExtendedEuclidean n) :
    Metric.infDist x {a,b} = min (chordalDist x a) (chordalDist x b) := by
  apply le_antisymm
  · exact le_min (Metric.infDist_le_dist_of_mem (by simp)) (Metric.infDist_le_dist_of_mem (by simp))
  · apply (Metric.le_infDist ⟨a,by simp⟩).mpr
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _

def puncturedFiniteDomain (a : Euclidean n) : Set (ExtendedEuclidean n) := {∞,(a : ExtendedEuclidean n)}ᶜ

theorem puncturedFiniteDomain_isOpen (a : Euclidean n) : IsOpen (puncturedFiniteDomain a) :=
  (Set.toFinite ({∞,(a : ExtendedEuclidean n)} : Set (ExtendedEuclidean n))).isClosed.isOpen_compl

theorem puncturedFiniteDomain_mem (a x : Euclidean n) : (x : ExtendedEuclidean n) ∈ puncturedFiniteDomain a ↔ x ≠
    a := by
  simp [puncturedFiniteDomain]

theorem puncturedFiniteDomain_infDist (a x : Euclidean n) :
    Metric.infDist (x : ExtendedEuclidean n) (puncturedFiniteDomain a)ᶜ =
      min (chordalDist (x : ExtendedEuclidean n) ∞) (chordalDist (x : ExtendedEuclidean n) a) := by
  rw [puncturedFiniteDomain,compl_compl,metric_infDist_pair]

theorem puncturedFiniteDomain_isPreconnected (hn : 2 ≤ n) (a : Euclidean n) :
    IsPreconnected (puncturedFiniteDomain a) := by
  have hdim : 1 < Module.finrank ℝ (Euclidean n) := by simpa using (show 1 < n by omega)
  have hconn := (isPathConnected_compl_singleton_of_one_lt_rank
    (Module.one_lt_rank_of_one_lt_finrank hdim) a).isConnected.isPreconnected
  have hh := hconn.image ((↑) : Euclidean n → ExtendedEuclidean n) OnePoint.continuous_coe.continuousOn
  convert hh using 1
  ext z
  induction z using OnePoint.rec with
  | infty => simp [puncturedFiniteDomain]
  | coe x => simp [puncturedFiniteDomain]

def ChordalOmissionBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ f : ExtendedHomeomorph n, f ∈ generalMobiusGroup n →
  ∀ D : Set (ExtendedEuclidean n), IsOpen D → IsPreconnected D →
  ∀ a b : ExtendedEuclidean n, a ≠ b → a ∉ f '' D → b ∉ f '' D →
  ∀ x y : ExtendedEuclidean n, x ∈ D → y ∈ D →
    chordalDist (f x) (f y) ≤ C * chordalDist x y /
      (chordalDist a b * Real.sqrt (Metric.infDist x (frontier D)) * Real.sqrt (Metric.infDist y (frontier D)))

theorem chordalOmissionBound_eight [NeZero n] : ChordalOmissionBound n 8 := by
  intro f hf D hD _ a b hab ha hb x y hx hy
  exact generalMobius_omitted_distortion_frontier f hf D hD a b hab ha hb x y hx hy

theorem ChordalOmissionBound.translation_local_lower [NeZero n] (hn : 2 ≤ n) {C : ℝ}
    (hC : ChordalOmissionBound n C) (v a x : Euclidean n) (hxa : x ≠ a) :
    ((1+‖x‖^2)/(1+‖x+v‖^2)) *
      (chordalDist (∞ : ExtendedEuclidean n) (a+v : Euclidean n) *
        Metric.infDist (x : ExtendedEuclidean n) (puncturedFiniteDomain a)ᶜ) ≤ C := by
  let D := puncturedFiniteDomain a
  let f := translationHomeomorph v
  have hD : IsOpen D := puncturedFiniteDomain_isOpen a
  have hconn : IsPreconnected D := puncturedFiniteDomain_isPreconnected hn a
  have hDc : Dᶜ.Nonempty := ⟨∞,by simp [D,puncturedFiniteDomain]⟩
  have hx : (x : ExtendedEuclidean n) ∈ D := (puncturedFiniteDomain_mem a x).mpr hxa
  have hfx : (∞ : ExtendedEuclidean n) ∉ f '' D := by
    rintro ⟨z,hz,he⟩
    have he' : z = ∞ := f.injective he
    subst z
    simp [D,puncturedFiniteDomain] at hz
  have hfa : ((a+v : Euclidean n) : ExtendedEuclidean n) ∉ f '' D := by
    rintro ⟨z,hz,he⟩
    have he' : z = (a : ExtendedEuclidean n) := f.injective he
    subst z
    exact ((puncturedFiniteDomain_mem a a).mp hz) rfl
  have hδpos : 0 < Metric.infDist (x : ExtendedEuclidean n) Dᶜ :=
    (hD.isClosed_compl.notMem_iff_infDist_pos hDc).mp (by simpa using hx)
  have hδcont : ContinuousAt (fun y : Euclidean n => Real.sqrt (Metric.infDist (y : ExtendedEuclidean n) Dᶜ)) x :=
    (((Metric.continuous_infDist_pt Dᶜ).comp OnePoint.continuous_coe).continuousAt).sqrt
  have hδlim := hδcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] x ≤ 𝓝 x)
  have hlim := (chordal_translation_ratio_limit v x).mul
    (((tendsto_const_nhds (x := chordalDist (∞ : ExtendedEuclidean n) (a+v : Euclidean n))).mul
      (tendsto_const_nhds (x := Real.sqrt (Metric.infDist (x : ExtendedEuclidean n) Dᶜ)))).mul hδlim)
  change Tendsto _ _ (𝓝 (((1+‖x‖^2)/(1+‖x+v‖^2)) *
    ((chordalDist (∞ : ExtendedEuclidean n) (a+v : Euclidean n) * Real.sqrt (Metric.infDist (x : ExtendedEuclidean
      n) Dᶜ)) *
      Real.sqrt (Metric.infDist (x : ExtendedEuclidean n) Dᶜ)))) at hlim
  rw [mul_assoc (chordalDist (∞ : ExtendedEuclidean n) (a+v : Euclidean n)),Real.mul_self_sqrt hδpos.le] at hlim
  apply le_of_tendsto hlim
  have hyEv : ∀ᶠ y : Euclidean n in 𝓝[≠] x, y ≠ a :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds hxa)
  filter_upwards [self_mem_nhdsWithin,hyEv] with y hyx hya
  have hy : (y : ExtendedEuclidean n) ∈ D := (puncturedFiniteDomain_mem a y).mpr hya
  have hδy : 0 < Metric.infDist (y : ExtendedEuclidean n) Dᶜ :=
    (hD.isClosed_compl.notMem_iff_infDist_pos hDc).mp (by simpa using hy)
  have hb := hC f (translation_mem_generalMobiusGroup v) D hD hconn ∞ (a+v : Euclidean n)
    (OnePoint.infty_ne_coe _) hfx hfa x y hx hy
  rw [chordal_infDist_frontier_eq_compl D hD hDc x hx,
    chordal_infDist_frontier_eq_compl D hD hDc y hy] at hb
  have hden : 0 < chordalDist (∞ : ExtendedEuclidean n) (a+v : Euclidean n) *
      Real.sqrt (Metric.infDist (x : ExtendedEuclidean n) Dᶜ) * Real.sqrt (Metric.infDist (y : ExtendedEuclidean
        n) Dᶜ) :=
    mul_pos (mul_pos (chordalDist_positive (OnePoint.infty_ne_coe _)) (Real.sqrt_pos.mpr hδpos)) (Real.sqrt_pos.mpr hδy)
  have hb' := (le_div_iff₀ hden).mp hb
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (chordalDist_positive (OnePoint.coe_injective.ne (Ne.symm hyx)))).mpr
  exact hb'

theorem norm_smul_unit {u : Euclidean n} (hu : ‖u‖ = 1) (t : ℝ) : ‖t • u‖ = |t| := by
  rw [norm_smul,Real.norm_eq_abs,hu,mul_one]

theorem dist_smul_unit {u : Euclidean n} (hu : ‖u‖ = 1) (t s : ℝ) : dist (t • u) (s • u) = |t-s| := by
  rw [dist_eq_norm,← sub_smul,norm_smul_unit hu]

theorem sharpTranslation_clearance {u : Euclidean n} (hu : ‖u‖ = 1) {m : ℝ} (hm : 0 < m) :
    Metric.infDist (((-2*m) • u : Euclidean n) : ExtendedEuclidean n) (puncturedFiniteDomain ((-m) • u))ᶜ =
      (2*m)/(Real.sqrt (1+4*m^2)*Real.sqrt (1+m^2)) := by
  rw [puncturedFiniteDomain_infDist,chordalDist_coe_infty,chordalDist_coe_coe,
    norm_smul_unit hu,norm_smul_unit hu,dist_smul_unit hu]
  have hpow : |-2*m|^2 = 4*m^2 := by rw [sq_abs]; ring
  have hpow' : |-m|^2 = m^2 := by rw [sq_abs]; ring
  have hdist : |-2*m- -m| = m := by rw [abs_of_neg (by linarith : -2*m- -m < 0)]; ring
  rw [hpow,hpow',hdist]
  apply min_eq_right
  have hs : m ≤ Real.sqrt (1+m^2) := Real.le_sqrt_of_sq_le (by linarith)
  have hA : 0 < Real.sqrt (1+4*m^2) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < Real.sqrt (1+m^2) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_div_iff₀ (mul_pos hA hB) hA).mpr
  nlinarith

theorem sharpTranslation_coefficient {u : Euclidean n} (hu : ‖u‖ = 1) {m : ℝ} (hm : 0 < m) :
    ((1+‖(-2*m) • u‖^2)/(1+‖(-2*m) • u+(2*m) • u‖^2)) *
      (chordalDist (∞ : ExtendedEuclidean n) ((-m) • u+(2*m) • u : Euclidean n) *
        Metric.infDist (((-2*m) • u : Euclidean n) : ExtendedEuclidean n) (puncturedFiniteDomain ((-m) • u))ᶜ) =
      4*m*Real.sqrt (1+4*m^2)/(1+m^2) := by
  have hadd : (-2*m) • u+(2*m) • u = 0 := by module
  have hadd' : (-m) • u+(2*m) • u = m • u := by module
  rw [hadd,hadd',norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,chordalDist_infty_coe,
    norm_smul_unit hu,norm_smul_unit hu,sharpTranslation_clearance hu hm]
  rw [sq_abs,sq_abs]
  have hpow : (-2*m)^2 = 4*m^2 := by ring
  rw [hpow]
  have hA : Real.sqrt (1+4*m^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hB : Real.sqrt (1+m^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hAsq := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1+4*m^2)
  have hBsq := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1+m^2)
  field_simp [hA,hB]
  nlinarith

theorem ChordalOmissionBound.translation_family_lower [NeZero n] (hn : 2 ≤ n) {C : ℝ}
    (hC : ChordalOmissionBound n C) (u : Euclidean n) (hu : ‖u‖ = 1) {m : ℝ} (hm : 0 < m) :
    4*m*Real.sqrt (1+4*m^2)/(1+m^2) ≤ C := by
  have hu0 : u ≠ 0 := by intro h; rw [h,norm_zero] at hu; norm_num at hu
  have hxa : (-2*m) • u ≠ (-m) • u := by
    intro h
    have he := smul_left_injective ℝ hu0 h
    linarith
  have hh := hC.translation_local_lower hn ((2*m) • u) ((-m) • u) ((-2*m) • u) hxa
  rwa [sharpTranslation_coefficient hu hm] at hh

theorem sharpTranslation_coefficient_normalized {m : ℝ} (hm : 0 < m) :
    4*m*Real.sqrt (1+4*m^2)/(1+m^2) = 4*Real.sqrt (4+(m⁻¹)^2)/(1+(m⁻¹)^2) := by
  have hs : Real.sqrt (1+4*m^2) = m*Real.sqrt (4+(m⁻¹)^2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hm.le (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    field_simp [hm.ne']
    ring
  rw [hs]
  field_simp [hm.ne']
  ring

theorem sharpTranslation_coefficient_limit :
    Tendsto (fun m : ℝ => 4*m*Real.sqrt (1+4*m^2)/(1+m^2)) atTop (𝓝 8) := by
  have hi : Tendsto (fun m : ℝ => m⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun m : ℝ => 4*Real.sqrt (4+(m⁻¹)^2)) atTop (𝓝 8) := by
    convert tendsto_const_nhds.mul ((tendsto_const_nhds.add (hi.pow 2)).sqrt) using 1; norm_num
  have hden : Tendsto (fun m : ℝ => 1+(m⁻¹)^2) atTop (𝓝 1) := by
    convert tendsto_const_nhds.add (hi.pow 2) using 1; norm_num
  have hh := hnum.div hden (by norm_num : (1:ℝ) ≠ 0)
  rw [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with m hm
  exact (sharpTranslation_coefficient_normalized hm).symm

/-- no smaller universal constant works, even for connected domains. -/
theorem chordalOmissionBound_least_constant [NeZero n] (hn : 2 ≤ n) :
    IsLeast {C : ℝ | ChordalOmissionBound n C} 8 := by
  refine ⟨chordalOmissionBound_eight,?_⟩
  intro C hC
  let i : Fin n := ⟨0,NeZero.pos n⟩
  let u : Euclidean n := EuclideanSpace.single i 1
  have hu : ‖u‖ = 1 := by simp [u]
  apply le_of_tendsto sharpTranslation_coefficient_limit
  filter_upwards [eventually_gt_atTop (0:ℝ)] with m hm
  exact hC.translation_family_lower hn u hu hm

def UniformChordalOmissionBound (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, ChordalOmissionBound n C

theorem uniformChordalOmissionBound_least_constant :
    IsLeast {C : ℝ | UniformChordalOmissionBound C} 8 := by
  refine ⟨fun n _ => chordalOmissionBound_eight,?_⟩
  intro C hC
  exact (chordalOmissionBound_least_constant (n := 2) (by omega)).2 (hC 2 inferInstance)

end Sharp
end LowDimensionalTopology.Geometry.Inversive
