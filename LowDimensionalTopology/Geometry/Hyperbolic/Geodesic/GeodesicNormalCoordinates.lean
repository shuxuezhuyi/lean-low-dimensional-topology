module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertQuadrilaterals
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- Two nonzero affine normals through the same two distinct actual planar points are proportional. -/
theorem complex_affine_normals_proportional (n m x y : ℂ) (t u : ℝ)
    (hn : n ≠ 0) (hm : m ≠ 0) (hxy : x ≠ y)
    (hnx : inner ℝ n x = t) (hny : inner ℝ n y = t)
    (hmx : inner ℝ m x = u) (hmy : inner ℝ m y = u) :
    ∃ k : ℝ, k ≠ 0 ∧ m = k • n ∧ u = k * t := by
  let d := y - x
  have hd : d ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hdN : inner ℝ d n = 0 := by
    rw [real_inner_comm n d]
    change inner ℝ n (y - x) = 0
    rw [inner_sub_right,hny,hnx,sub_self]
  have hMd : inner ℝ m d = 0 := by
    change inner ℝ m (y - x) = 0
    rw [inner_sub_right,hmy,hmx,sub_self]
  have hg := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_gram_three d n m
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hdN,hMd] at hg
  have hn2 : ‖n‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  have hprod : ‖n‖ ^ 2 * ‖m‖ ^ 2 = inner ℝ n m ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd))
    nlinarith only [hg]
  let k := inner ℝ n m / ‖n‖ ^ 2
  have hdiff : ‖m - k • n‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right,
      real_inner_comm n m]
    dsimp only [k]
    field_simp
    nlinarith only [hprod]
  have hmn : m = k • n := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdiff))
  have hk : k ≠ 0 := by
    intro he
    exact hm (by rw [hmn,he,zero_smul])
  refine ⟨k,hk,hmn,?_⟩
  rw [hmn,real_inner_smul_left,hnx] at hmx
  exact hmx.symm

/-- Normalizing the actual affine equations by the Lorentz unit equation leaves only a sign. -/
theorem complex_affine_lorentz_normals_sign (n m x y : ℂ) (t u : ℝ)
    (hn : ‖n‖ ^ 2 - t ^ 2 = 1) (hm : ‖m‖ ^ 2 - u ^ 2 = 1) (hxy : x ≠ y)
    (hnx : inner ℝ n x = t) (hny : inner ℝ n y = t)
    (hmx : inner ℝ m x = u) (hmy : inner ℝ m y = u) :
    ∃ k : ℝ, k ^ 2 = 1 ∧ m = k • n ∧ u = k * t := by
  have hn0 : n ≠ 0 := by
    intro he
    rw [he,norm_zero,zero_pow (by omega : 2 ≠ 0),zero_sub] at hn
    nlinarith only [hn,sq_nonneg t]
  have hm0 : m ≠ 0 := by
    intro he
    rw [he,norm_zero,zero_pow (by omega : 2 ≠ 0),zero_sub] at hm
    nlinarith only [hm,sq_nonneg u]
  obtain ⟨k,_,hmn,htu⟩ := complex_affine_normals_proportional n m x y t u hn0 hm0 hxy hnx hny hmx hmy
  refine ⟨k,?_,hmn,htu⟩
  rw [hmn,htu,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_pow] at hm
  nlinarith only [hm,hn]

/-- Exact pairing transport for any two normalized representations of the actual side equations. -/
theorem normalized_side_pairing_sign (n₁ n₂ m₁ m₂ : ℂ) (t₁ t₂ u₁ u₂ k₁ k₂ : ℝ)
    (hk₁ : k₁ ^ 2 = 1) (hk₂ : k₂ ^ 2 = 1)
    (hn₁ : m₁ = k₁ • n₁) (hn₂ : m₂ = k₂ • n₂)
    (ht₁ : u₁ = k₁ * t₁) (ht₂ : u₂ = k₂ * t₂) :
    |inner ℝ m₁ m₂ - u₁ * u₂| = |inner ℝ n₁ n₂ - t₁ * t₂| := by
  have h₁ : |k₁| = 1 := by nlinarith only [hk₁,sq_abs k₁,abs_nonneg k₁]
  have h₂ : |k₂| = 1 := by nlinarith only [hk₂,sq_abs k₂,abs_nonneg k₂]
  rw [hn₁,hn₂,ht₁,ht₂,real_inner_smul_left,inner_smul_right]
  calc
    _ = |k₁ * k₂ * (inner ℝ n₁ n₂ - t₁ * t₂)| := by congr 1; ring
    _ = _ := by rw [abs_mul,abs_mul,h₁,h₂,one_mul,one_mul]

/-- Any normalized actual Klein side equation agrees with the genuine native side normal up to sign. -/
theorem DiscLine.normalized_equation_sign (L : DiscLine) (n : ℂ) (t : ℝ)
    (hn : ‖n‖ ^ 2 - t ^ 2 = 1)
    (hL : ∀ z ∈ L.carrier, inner ℝ n (kleinCoordinate z) = t) :
    ∃ k : ℝ, k ^ 2 = 1 ∧ n = k • L.incenterNormal ∧ t = k * L.incenterOffset := by
  obtain ⟨a,b,ha,hb,hab⟩ := L.toHalfPlane.exists_two_points
  let u := halfPlaneToDisc a
  let v := halfPlaneToDisc b
  have hu : u ∈ L.carrier := (L.mem_carrier _).mpr
    (by simpa only [u,discToHalfPlane_halfPlaneToDisc] using ha)
  have hv : v ∈ L.carrier := (L.mem_carrier _).mpr
    (by simpa only [v,discToHalfPlane_halfPlaneToDisc] using hb)
  have huv : kleinCoordinate u ≠ kleinCoordinate v := by
    intro he
    exact hab ((show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)
      (kleinCoordinate_injective he))
  exact complex_affine_lorentz_normals_sign L.incenterNormal n (kleinCoordinate u) (kleinCoordinate v)
    L.incenterOffset t L.toHalfPlane.incenterNormal_lorentz_unit hn huv
    ((L.incenter_affine_eq_zero_iff u).mpr hu) ((L.incenter_affine_eq_zero_iff v).mpr hv)
    (hL u hu) (hL v hv)

/-- Arbitrary normalized equations of the actual sides recover the original geometric product. -/
theorem DiscLine.inversiveProduct_normalized_equations (L M : DiscLine) (n m : ℂ) (t u : ℝ)
    (hn : ‖n‖ ^ 2 - t ^ 2 = 1) (hm : ‖m‖ ^ 2 - u ^ 2 = 1)
    (hL : ∀ z ∈ L.carrier, inner ℝ n (kleinCoordinate z) = t)
    (hM : ∀ z ∈ M.carrier, inner ℝ m (kleinCoordinate z) = u) :
    |inner ℝ n m - t * u| = Inversive.inversiveProduct L.val.realModel M.val.realModel := by
  obtain ⟨k,hk,hnk,htk⟩ := L.normalized_equation_sign n t hn hL
  obtain ⟨l,hl,hml,hul⟩ := M.normalized_equation_sign m u hm hM
  rw [disc_inversiveProduct_eq_halfPlane,halfPlane_inversiveProduct_eq_normal_product]
  exact normalized_side_pairing_sign L.incenterNormal M.incenterNormal n m
    L.incenterOffset M.incenterOffset t u k l hk hl hnk hml htk hul

/-- Genuine inward normalized equations encode the actual finite or ideal corner angle. -/
theorem ClosedDiscTriangle.cosine_alpha_inward_normalized_equations
    (T : ClosedDiscTriangle) (q : 𝔻) (n m : ℂ) (t u : ℝ)
    (hq : 0 < (T.discCoordinate q).1 ∧ 0 < (T.discCoordinate q).2)
    (hn : ‖n‖ ^ 2 - t ^ 2 = 1) (hm : ‖m‖ ^ 2 - u ^ 2 = 1)
    (hB : ∀ z ∈ T.sideLineB.carrier, inner ℝ n (kleinCoordinate z) = t)
    (hC : ∀ z ∈ T.sideLineC.carrier, inner ℝ m (kleinCoordinate z) = u)
    (hqn : 0 < inner ℝ n (kleinCoordinate q) - t)
    (hqm : 0 < inner ℝ m (kleinCoordinate q) - u) :
    inner ℝ n m - t * u = -Real.cos T.alpha := by
  obtain ⟨k,hk,hnk,htk⟩ := T.sideLineB.normalized_equation_sign n t hn hB
  obtain ⟨l,hl,hml,hul⟩ := T.sideLineC.normalized_equation_sign m u hm hC
  let F := closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (discToClosedModel q)
  let G := closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (discToClosedModel q)
  let B := inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
    T.sideLineB.incenterOffset * T.sideLineC.incenterOffset
  have hqn' : 0 < k * F := by
    rw [hnk,htk,real_inner_smul_left] at hqn
    simpa only [F,closedDiscKleinAffine,closedKleinCoordinate_disc_inclusion,mul_sub] using hqn
  have hqm' : 0 < l * G := by
    rw [hml,hul,real_inner_smul_left] at hqm
    simpa only [G,closedDiscKleinAffine,closedKleinCoordinate_disc_inclusion,mul_sub] using hqm
  have hak : |k| = 1 := by nlinarith only [hk,sq_abs k,abs_nonneg k]
  have hal : |l| = 1 := by nlinarith only [hl,sq_abs l,abs_nonneg l]
  have hF : |F| = k * F := by
    have he := abs_of_pos hqn'
    rw [abs_mul,hak,one_mul] at he
    exact he
  have hG : |G| = l * G := by
    have he := abs_of_pos hqm'
    rw [abs_mul,hal,one_mul] at he
    exact he
  have he := T.cosine_alpha_side_normals_of_positive_coordinates q hq
  change Real.cos T.alpha * |F| * |G| = -(B * F * G) at he
  rw [hF,hG] at he
  have hkl : (k * l) ^ 2 = 1 := by rw [mul_pow,hk,hl,one_mul]
  have hmulteq := congrArg (fun x : ℝ => k * l * x) he
  have hunit := congrArg (fun x : ℝ => Real.cos T.alpha * F * G * x) hkl
  have hFG : F * G ≠ 0 := mul_ne_zero ((mul_pos_iff.mp hqn').elim (fun h => h.2.ne') (fun h => h.2.ne))
    ((mul_pos_iff.mp hqm').elim (fun h => h.2.ne') (fun h => h.2.ne))
  have hpair : k * l * B = -Real.cos T.alpha := by
    apply mul_right_cancel₀ hFG
    nlinarith only [hmulteq,hunit]
  rw [hnk,hml,htk,hul,real_inner_smul_left,inner_smul_right]
  calc
    _ = k * l * B := by dsimp only [B]; ring
    _ = _ := hpair

end
end LowDimensionalTopology.Geometry.Hyperbolic
