/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Group
public import LowDimensionalTopology.Geometry.Euclidean.EuclideanIsometries
public import LowDimensionalTopology.Geometry.Inversive.Bracket
/-!
# The real cross ratio

The chordal cross ratio is `d(x,u) * d(y,v) / (d(x,y) * d(u,v))`.
Its Euclidean expression and each position of infinity are verified explicitly.
Preservation by an arbitrary map forces injectivity; normalization at infinity
then yields a Euclidean similarity, without extra continuity or bijectivity assumptions.
-/

@[expose] public section
noncomputable section
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

def realCrossRatio (x y u v : ExtendedEuclidean n) : ℝ :=
  chordalDist x u*chordalDist y v/(chordalDist x y*chordalDist u v)

def FourDistinct (x y u v : ExtendedEuclidean n) : Prop :=
  x ≠ y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v ∧ u ≠ v

def PreservesRealCrossRatios (f : ExtendedEuclidean n → ExtendedEuclidean n) : Prop :=
  ∀ x y u v, FourDistinct x y u v →
    realCrossRatio (f x) (f y) (f u) (f v)=realCrossRatio x y u v

theorem chordalDist_symm (x y : ExtendedEuclidean n) : chordalDist x y=chordalDist y x :=
  dist_comm _ _

theorem chordalDist_positive {x y : ExtendedEuclidean n} (h : x ≠ y) : 0<chordalDist x y :=
  dist_pos.mpr ((stereographicHomeomorph n).injective.ne h)

theorem realCrossRatio_positive {x y u v : ExtendedEuclidean n} (h : FourDistinct x y u v) :
    0<realCrossRatio x y u v :=
  div_pos (mul_pos (chordalDist_positive h.2.1) (chordalDist_positive h.2.2.2.2.1))
    (mul_pos (chordalDist_positive h.1) (chordalDist_positive h.2.2.2.2.2))

theorem chordalDist_infty_coe (x : Euclidean n) :
    chordalDist (∞ : ExtendedEuclidean n) x=2/Real.sqrt (1+‖x‖^2) := by
  rw [chordalDist_symm, chordalDist_coe_infty]

theorem realCrossRatio_finite (x y u v : Euclidean n) (hxy : x ≠ y) (huv : u ≠ v) :
    realCrossRatio (n := n) x y u v=dist x u*dist y v/(dist x y*dist u v) := by
  unfold realCrossRatio
  rw [chordalDist_coe_coe, chordalDist_coe_coe, chordalDist_coe_coe, chordalDist_coe_coe]
  have hX : Real.sqrt (1+‖x‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hY : Real.sqrt (1+‖y‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hU : Real.sqrt (1+‖u‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hV : Real.sqrt (1+‖v‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hX,hY,hU,hV,dist_ne_zero.mpr hxy,dist_ne_zero.mpr huv]

theorem realCrossRatio_infty_first (y u v : Euclidean n) (huv : u ≠ v) :
    realCrossRatio (∞ : ExtendedEuclidean n) y u v=dist y v/dist u v := by
  unfold realCrossRatio
  rw [chordalDist_infty_coe, chordalDist_coe_coe, chordalDist_infty_coe, chordalDist_coe_coe]
  have hY : Real.sqrt (1+‖y‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hU : Real.sqrt (1+‖u‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hV : Real.sqrt (1+‖v‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hY,hU,hV,dist_ne_zero.mpr huv]

theorem realCrossRatio_swap_pairs (x y u v : ExtendedEuclidean n) :
    realCrossRatio x y u v=realCrossRatio u v x y := by
  unfold realCrossRatio
  rw [chordalDist_symm x u,chordalDist_symm y v]
  ring

theorem realCrossRatio_reverse_pairs (x y u v : ExtendedEuclidean n) :
    realCrossRatio x y u v=realCrossRatio y x v u := by
  unfold realCrossRatio
  rw [chordalDist_symm y x,chordalDist_symm v u]
  ring

theorem realCrossRatio_infty_second (x u v : Euclidean n) (huv : u ≠ v) :
    realCrossRatio x (∞ : ExtendedEuclidean n) u v=dist x u/dist u v := by
  rw [realCrossRatio_reverse_pairs, realCrossRatio_infty_first _ _ _ huv.symm, dist_comm v u]

theorem realCrossRatio_infty_third (x y v : Euclidean n) (hxy : x ≠ y) :
    realCrossRatio x y (∞ : ExtendedEuclidean n) v=dist y v/dist x y := by
  rw [realCrossRatio_swap_pairs, realCrossRatio_infty_first _ _ _ hxy, dist_comm v y]

theorem realCrossRatio_infty_fourth (x y u : Euclidean n) (hxy : x ≠ y) :
    realCrossRatio x y u (∞ : ExtendedEuclidean n)=dist x u/dist x y := by
  rw [realCrossRatio_reverse_pairs, realCrossRatio_infty_third _ _ _ hxy.symm, dist_comm y x]


theorem PreservesRealCrossRatios.injective [NeZero n]
    {f : ExtendedEuclidean n → ExtendedEuclidean n} (hf : PreservesRealCrossRatios f) :
    Function.Injective f := by
  classical
  intro x u hfu
  by_contra hxu
  obtain ⟨y, hy⟩ := Finset.exists_notMem ({x,u} : Finset (ExtendedEuclidean n))
  obtain ⟨v, hv⟩ := Finset.exists_notMem ({x,y,u} : Finset (ExtendedEuclidean n))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy hv
  have hd : FourDistinct x y u v :=
    ⟨Ne.symm hy.1,hxu,Ne.symm hv.1,hy.2,Ne.symm hv.2.1,Ne.symm hv.2.2⟩
  have hpos := realCrossRatio_positive hd
  have hzero := hf x y u v hd
  rw [realCrossRatio,hfu] at hzero
  have hself : chordalDist (f u) (f u)=0 := dist_self _
  rw [hself,zero_mul,zero_div] at hzero
  linarith


theorem PreservesRealCrossRatios.fixing_infty_similarity [NeZero n]
    {f : ExtendedEuclidean n → ExtendedEuclidean n} (hf : PreservesRealCrossRatios f)
    (hinfty : f ∞=∞) :
    ∃ k : ℝ, ∃ φ : Euclidean n ≃ᵢ Euclidean n,
      0<k ∧ ∀ x : Euclidean n, f x=(((k • (φ x : Euclidean n)) : Euclidean n) : ExtendedEuclidean n) := by
  classical
  have hfin : ∀ x : Euclidean n, ∃ z : Euclidean n, (z : ExtendedEuclidean n)=f x := by
    intro x
    apply OnePoint.ne_infty_iff_exists.mp
    intro h
    exact OnePoint.coe_ne_infty x (hf.injective (h.trans hinfty.symm))
  choose F hF using hfin
  have hFi : Function.Injective F := by
    intro x y h
    apply OnePoint.coe_injective
    apply hf.injective
    rw [←hF x,←hF y,h]
  have hratio (x y u : Euclidean n) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u) :
      dist (F x) (F u)/dist (F x) (F y)=dist x u/dist x y := by
    have hd : FourDistinct (x : ExtendedEuclidean n) y u ∞ := by
      exact ⟨OnePoint.coe_injective.ne hxy,OnePoint.coe_injective.ne hxu,
        OnePoint.coe_ne_infty x,OnePoint.coe_injective.ne hyu,
        OnePoint.coe_ne_infty y,OnePoint.coe_ne_infty u⟩
    have h := hf x y u ∞ hd
    rw [←hF x,←hF y,←hF u,hinfty,
      realCrossRatio_infty_fourth _ _ _ (hFi.ne hxy),
      realCrossRatio_infty_fourth _ _ _ hxy] at h
    exact h
  obtain ⟨a, ha⟩ := exists_ne (0 : Euclidean n)
  let k := dist (F 0) (F a)/dist (0 : Euclidean n) a
  have hk : 0<k := div_pos (dist_pos.mpr (hFi.ne (Ne.symm ha)))
    (dist_pos.mpr (Ne.symm ha))
  have hrad (x : Euclidean n) : dist (F 0) (F x)=k*dist (0 : Euclidean n) x := by
    by_cases hx : x=0
    · simp [hx]
    by_cases hxa : x=a
    · subst x
      dsimp [k]
      exact (div_mul_cancel₀ _ (dist_ne_zero.mpr (Ne.symm ha))).symm
    have h := hratio 0 a x (Ne.symm ha) (Ne.symm hx) (Ne.symm hxa)
    dsimp [k]
    field_simp [dist_ne_zero.mpr (hFi.ne (Ne.symm ha)),dist_ne_zero.mpr (Ne.symm ha)] at h ⊢
    nlinarith
  have hdist (x y : Euclidean n) : dist (F x) (F y)=k*dist x y := by
    by_cases hxy : x=y
    · simp [hxy]
    by_cases hx : x=0
    · subst x
      exact hrad y
    by_cases hy : y=0
    · subst y
      simpa only [dist_comm] using hrad x
    have h := hratio x 0 y hx hxy (Ne.symm hy)
    have hr : dist (F x) (F 0)=k*dist x 0 := by
      simpa only [dist_comm] using hrad x
    rw [div_eq_iff (dist_ne_zero.mpr (hFi.ne hx))] at h
    rw [h,hr]
    calc
      (dist x y/dist x 0)*(k*dist x 0)=k*((dist x y/dist x 0)*dist x 0) := by ring
      _ = k*dist x y := by rw [div_mul_cancel₀ _ (dist_ne_zero.mpr hx)]
  let G : Euclidean n → Euclidean n := fun x => k⁻¹ • F x
  have hG : Isometry G := by
    apply Isometry.of_dist_eq
    intro x y
    dsimp [G]
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk),hdist]
    field_simp
  refine ⟨k,euclideanIsometryEquiv G hG,hk,?_⟩
  intro x
  rw [←hF x,euclideanIsometryEquiv_apply]
  congr 1
  dsimp [G]
  rw [smul_smul,mul_inv_cancel₀ hk.ne',one_smul]


theorem sqrt_unitInversion (x : Euclidean n) (hx : x ≠ 0) :
    Real.sqrt (1+‖unitInversion x‖^2)=Real.sqrt (1+‖x‖^2)/‖x‖ := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity),div_pow,Real.sq_sqrt (by positivity),norm_unitInversion]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

theorem chordalDist_unitSphere_infty_coe (x : Euclidean n) :
    chordalDist (sphereInversion (n := n) 0 1 (∞ : ExtendedEuclidean n)) (sphereInversion (n := n) 0 1 x)=
      chordalDist (∞ : ExtendedEuclidean n) x := by
  by_cases hx : x=0
  · subst x
    simp only [sphereInversion_infty,sphereInversion_center,
      chordalDist_coe_infty,chordalDist_infty_coe,norm_zero,zero_pow,ne_eq,
      OfNat.ofNat_ne_zero,not_false_eq_true,add_zero,Real.sqrt_one,div_one]
  · rw [sphereInversion_infty,sphereInversion_coe 0 1 hx,inversion_unit,
      chordalDist_coe_coe,chordalDist_infty_coe]
    simp only [dist_zero_left,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,add_zero,Real.sqrt_one,one_mul]
    rw [sqrt_unitInversion x hx,norm_unitInversion]
    field_simp [norm_ne_zero_iff.mpr hx]

theorem chordalDist_unitSphere_coe_coe {x y : Euclidean n} (hx : x ≠ 0) (hy : y ≠ 0) :
    chordalDist (sphereInversion (n := n) 0 1 x) (sphereInversion (n := n) 0 1 y)=
      chordalDist (x : ExtendedEuclidean n) y := by
  rw [sphereInversion_coe 0 1 hx,sphereInversion_coe 0 1 hy,inversion_unit,inversion_unit,
    chordalDist_coe_coe,chordalDist_coe_coe,sqrt_unitInversion x hx,sqrt_unitInversion y hy]
  have hd : dist (unitInversion x) (unitInversion y)=dist x y/(‖x‖*‖y‖) := by
    simpa only [inversion_unit,one_pow,dist_zero_right,one_div,mul_comm,div_eq_mul_inv,one_mul] using
      (sphereInversion_dist 1 hx hy)
  rw [hd]
  field_simp [norm_ne_zero_iff.mpr hx,norm_ne_zero_iff.mpr hy]

theorem chordalDist_unitSphere (x y : ExtendedEuclidean n) :
    chordalDist (sphereInversion (n := n) 0 1 x) (sphereInversion (n := n) 0 1 y)=chordalDist x y := by
  have hi (y : ExtendedEuclidean n) :
      chordalDist (sphereInversion (n := n) 0 1 (∞ : ExtendedEuclidean n)) (sphereInversion (n := n) 0 1 y)=
        chordalDist (∞ : ExtendedEuclidean n) y := by
    induction y using OnePoint.rec with
    | infty => simp [chordalDist, sphereInversion_infty]
    | coe y => exact chordalDist_unitSphere_infty_coe y
  have hz (y : ExtendedEuclidean n) :
      chordalDist (sphereInversion (n := n) 0 1 (0 : Euclidean n)) (sphereInversion (n := n) 0 1 y)=
        chordalDist (0 : Euclidean n) y := by
    have h := hi (sphereInversion (n := n) 0 1 y)
    rw [sphereInversion_infty,sphereInversion_involutive 0 one_ne_zero] at h
    rw [sphereInversion_center]
    exact h.symm
  induction x using OnePoint.rec with
  | infty => exact hi y
  | coe x =>
    induction y using OnePoint.rec with
    | infty => simpa only [chordalDist_symm] using hi (x : ExtendedEuclidean n)
    | coe y =>
      by_cases hx : x=0
      · subst x; exact hz y
      by_cases hy : y=0
      · subst y; simpa only [chordalDist_symm] using hz (x : ExtendedEuclidean n)
      exact chordalDist_unitSphere_coe_coe hx hy

theorem unitSphere_preservesRealCrossRatios :
    PreservesRealCrossRatios (sphereInversion (0 : Euclidean n) 1) := by
  intro x y u v _
  simp only [realCrossRatio,chordalDist_unitSphere]


theorem realCrossRatio_finite_all (x y u v : Euclidean n) :
    realCrossRatio (n := n) x y u v=dist x u*dist y v/(dist x y*dist u v) := by
  by_cases hxy : x=y
  · subst y; simp [realCrossRatio,chordalDist]
  by_cases huv : u=v
  · subst v; simp [realCrossRatio,chordalDist]
  exact realCrossRatio_finite x y u v hxy huv

theorem realCrossRatio_infty_first_all (y u v : Euclidean n) :
    realCrossRatio (∞ : ExtendedEuclidean n) y u v=dist y v/dist u v := by
  by_cases huv : u=v
  · subst v; simp [realCrossRatio,chordalDist]
  exact realCrossRatio_infty_first y u v huv

theorem realCrossRatio_infty_second_all (x u v : Euclidean n) :
    realCrossRatio x (∞ : ExtendedEuclidean n) u v=dist x u/dist u v := by
  rw [realCrossRatio_reverse_pairs,realCrossRatio_infty_first_all,dist_comm v u]

theorem realCrossRatio_infty_third_all (x y v : Euclidean n) :
    realCrossRatio x y (∞ : ExtendedEuclidean n) v=dist y v/dist x y := by
  rw [realCrossRatio_swap_pairs,realCrossRatio_infty_first_all,dist_comm v y]

theorem realCrossRatio_infty_fourth_all (x y u : Euclidean n) :
    realCrossRatio x y u (∞ : ExtendedEuclidean n)=dist x u/dist x y := by
  rw [realCrossRatio_reverse_pairs,realCrossRatio_infty_third_all,dist_comm y x]

theorem preservesRealCrossRatios_of_similarity {f : ExtendedEuclidean n → ExtendedEuclidean n}
    (F : Euclidean n → Euclidean n) {k : ℝ} (hk : k ≠ 0)
    (hinfty : f ∞=∞) (hfinite : ∀ x : Euclidean n, f x=(F x : ExtendedEuclidean n))
    (hdist : ∀ x y, dist (F x) (F y)=k*dist x y) : PreservesRealCrossRatios f := by
  intro x y u v hd
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    induction u using OnePoint.rec <;> induction v using OnePoint.rec
  all_goals simp [FourDistinct] at hd
  all_goals simp only [hinfty,hfinite]
  all_goals first
    | (rw [realCrossRatio_finite_all,realCrossRatio_finite_all]
       simp only [hdist]
       rw [mul_mul_mul_comm k _ k _,mul_mul_mul_comm k _ k _]
       exact mul_div_mul_left _ _ (mul_ne_zero hk hk))
    | (rw [realCrossRatio_infty_first_all,realCrossRatio_infty_first_all]
       simp only [hdist]
       exact mul_div_mul_left _ _ hk)
    | (rw [realCrossRatio_infty_second_all,realCrossRatio_infty_second_all]
       simp only [hdist]
       exact mul_div_mul_left _ _ hk)
    | (rw [realCrossRatio_infty_third_all,realCrossRatio_infty_third_all]
       simp only [hdist]
       exact mul_div_mul_left _ _ hk)
    | (rw [realCrossRatio_infty_fourth_all,realCrossRatio_infty_fourth_all]
       simp only [hdist]
       exact mul_div_mul_left _ _ hk)

theorem PreservesRealCrossRatios.comp {f g : ExtendedEuclidean n → ExtendedEuclidean n}
    (hf : PreservesRealCrossRatios f) (hg : PreservesRealCrossRatios g)
    (hgi : Function.Injective g) : PreservesRealCrossRatios (f ∘ g) := by
  intro x y u v hd
  have hdg : FourDistinct (g x) (g y) (g u) (g v) :=
    ⟨hgi.ne hd.1,hgi.ne hd.2.1,hgi.ne hd.2.2.1,hgi.ne hd.2.2.2.1,
      hgi.ne hd.2.2.2.2.1,hgi.ne hd.2.2.2.2.2⟩
  exact (hf _ _ _ _ hdg).trans (hg _ _ _ _ hd)

theorem PreservesRealCrossRatios.mul {f g : ExtendedHomeomorph n}
    (hf : PreservesRealCrossRatios f) (hg : PreservesRealCrossRatios g) :
    PreservesRealCrossRatios (f*g) := by
  exact hf.comp hg g.injective


theorem PreservesRealCrossRatios.inv {f : ExtendedHomeomorph n}
    (hf : PreservesRealCrossRatios f) : PreservesRealCrossRatios (f⁻¹ : ExtendedHomeomorph n) := by
  intro x y u v hd
  have hdg : FourDistinct (f⁻¹ x) (f⁻¹ y) (f⁻¹ u) (f⁻¹ v) :=
    ⟨f.symm.injective.ne hd.1,f.symm.injective.ne hd.2.1,f.symm.injective.ne hd.2.2.1,
      f.symm.injective.ne hd.2.2.2.1,f.symm.injective.ne hd.2.2.2.2.1,
      f.symm.injective.ne hd.2.2.2.2.2⟩
  simpa using (hf _ _ _ _ hdg).symm

theorem similarity_preservesRealCrossRatios (a : Euclidean n) (r : ℝ) (hr : 0<r) :
    PreservesRealCrossRatios (similarityHomeomorph a r hr.ne') := by
  apply preservesRealCrossRatios_of_similarity (fun x => r • x+a) hr.ne'
    (similarityHomeomorph_infty a r hr.ne') (similarityHomeomorph_coe a r hr.ne')
  intro x y
  rw [dist_add_right,dist_smul₀,Real.norm_eq_abs,abs_of_pos hr]

theorem euclideanIsometry_preservesRealCrossRatios (F : Euclidean n → Euclidean n)
    (hF : Isometry F) : PreservesRealCrossRatios (euclideanIsometryHomeomorph F hF) := by
  apply preservesRealCrossRatios_of_similarity F one_ne_zero
    (euclideanIsometryHomeomorph_infty F hF) (euclideanIsometryHomeomorph_coe F hF)
  intro x y
  simpa only [one_mul] using hF.dist_eq x y

theorem IsReflection.preservesRealCrossRatios {f : ExtendedHomeomorph n}
    (hf : IsReflection f) : PreservesRealCrossRatios f := by
  rcases hf with ⟨c,r,hr,rfl⟩ | ⟨a,t,ha,rfl⟩
  · rw [sphereInversion_similarity_conjugacy c r hr]
    have hI : PreservesRealCrossRatios (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero) :=
      unitSphere_preservesRealCrossRatios
    exact ((similarity_preservesRealCrossRatios c r hr).mul hI).mul
      (similarity_preservesRealCrossRatios c r hr).inv
  · apply preservesRealCrossRatios_of_similarity (planeReflectionFinite a t) one_ne_zero
      (by rfl) (by intro x; rfl)
    intro x y
    simpa only [planeReflectionFiniteIsometry_apply,one_mul] using
      (planeReflectionFiniteIsometry a t).dist_eq x y

theorem generalMobius_preservesRealCrossRatios (g : ExtendedHomeomorph n)
    (hg : g ∈ generalMobiusGroup n) : PreservesRealCrossRatios g := by
  obtain ⟨l,hl,rfl⟩ := (mem_generalMobiusGroup_iff g).mp hg
  have H : ∀ l : List (ExtendedHomeomorph n), (∀ g ∈ l, IsReflection g) →
      PreservesRealCrossRatios l.prod := by
    intro l
    induction l with
    | nil => intro _ x y u v _; rfl
    | cons g l ih =>
      intro hl
      rw [List.prod_cons]
      exact (hl g (by simp)).preservesRealCrossRatios.mul
        (ih (fun h hh => hl h (by simp [hh])))
  exact H l hl

theorem preservesRealCrossRatios_iff_generalMobius [NeZero n]
    (f : ExtendedEuclidean n → ExtendedEuclidean n) :
    PreservesRealCrossRatios f ↔
      ∃ g : ExtendedHomeomorph n, g ∈ generalMobiusGroup n ∧ (g : _ → _)=f := by
  constructor
  · intro hf
    obtain ⟨R,hR,hRi⟩ : ∃ R : ExtendedHomeomorph n,
        R ∈ generalMobiusGroup n ∧ R (f ∞)=∞ := by
      induction h : f ∞ using OnePoint.rec with
      | infty => exact ⟨1,(generalMobiusGroup n).one_mem,by rfl⟩
      | coe c =>
        refine ⟨sphereInversionHomeomorph c 1 one_ne_zero,
          (sphereInversion_isReflection c 1 zero_lt_one).mem_generalMobiusGroup,?_⟩
        simp only [sphereInversionHomeomorph_apply,sphereInversion_center]
    have hRF : PreservesRealCrossRatios (R ∘ f) :=
      (generalMobius_preservesRealCrossRatios R hR).comp hf hf.injective
    obtain ⟨k,φ,hk,hφ⟩ := hRF.fixing_infty_similarity hRi
    let S : ExtendedHomeomorph n := dilationHomeomorph k hk.ne' *
      euclideanIsometryHomeomorph φ φ.isometry
    have hS : S ∈ generalMobiusGroup n :=
      (generalMobiusGroup n).mul_mem (dilation_mem_generalMobiusGroup k hk)
        (euclideanIsometry_mem_generalMobiusGroup φ φ.isometry)
    have hSf (z : ExtendedEuclidean n) : S z=R (f z) := by
      induction z using OnePoint.rec with
      | infty => change ∞=R (f ∞); exact hRi.symm
      | coe x => exact (hφ x).symm
    refine ⟨R⁻¹*S,(generalMobiusGroup n).mul_mem ((generalMobiusGroup n).inv_mem hR) hS,?_⟩
    funext z
    change R.symm (S z)=f z
    rw [hSf,R.symm_apply_apply]
  · rintro ⟨g,hg,rfl⟩
    exact generalMobius_preservesRealCrossRatios g hg

end LowDimensionalTopology.Geometry.Inversive
