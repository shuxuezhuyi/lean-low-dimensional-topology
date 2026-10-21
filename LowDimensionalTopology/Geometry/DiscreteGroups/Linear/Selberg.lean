module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.RingTheory.Finiteness.Cardinality

@[expose] public section

namespace LowDimensionalTopology.Geometry.DiscreteGroups

open Matrix

variable {R K ι : Type*} [CommRing R] [IsDomain R] [Field K]
  [Fintype ι] [DecidableEq ι]

/-- A finite-order congruence matrix is trivial when its order is nonzero in the residue field. -/
theorem congruence_pow_eq_one (f : R →+* K) (A : Matrix ι ι R) (n : ℕ)
    (hred : A.map f = 1) (hpow : A ^ n = 1) (hn : (n : K) ≠ 0) : A = 1 := by
  let B : Matrix ι ι R := ∑ k ∈ Finset.range n, A ^ k
  have hB : B.map f = (n : K) • (1 : Matrix ι ι K) := by
    change (f.mapMatrix : Matrix ι ι R →+* Matrix ι ι K) B = _
    simp only [B, map_sum, map_pow]
    change (∑ k ∈ Finset.range n, (A.map f) ^ k) = _
    simp [hred, Nat.cast_smul_eq_nsmul]
  have hdet : B.det ≠ 0 := by
    intro hzero
    have hmap : (B.map f).det = 0 := by
      change (f.mapMatrix B).det = 0
      rw [← RingHom.map_det, hzero, map_zero]
    have : (n : K) ^ Fintype.card ι = 0 := by
      simpa only [hB, Matrix.det_smul, Matrix.det_one, mul_one] using hmap
    exact (pow_ne_zero _ hn) this
  have hprod : (A - 1) * B = 0 := by
    simpa [B, hpow] using mul_geom_sum A n
  have hscalar : B.det • (A - 1) = 0 := by
    have h := congrArg (fun X => X * B.adjugate) hprod
    simpa [mul_assoc, Matrix.mul_adjugate] using h
  exact sub_eq_zero.mp ((smul_eq_zero.mp hscalar).resolve_left hdet)

/-- A prime-order element in a congruence kernel has the residue characteristic. -/
theorem congruence_prime_order_characteristic (f : R →+* K)
    (A : Matrix.GeneralLinearGroup ι R) (p : ℕ) (hp : p.Prime)
    (hred : Matrix.GeneralLinearGroup.map f A = 1) (horder : orderOf A = p) :
    ringChar K = p := by
  apply CharP.ringChar_of_prime_eq_zero hp
  by_contra hcast
  have hA : (A : Matrix ι ι R) = 1 := congruence_pow_eq_one f A p
    (by exact congrArg Units.val hred)
    (by simpa only [← horder, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val (pow_orderOf_eq_one A)) hcast
  have : A = 1 := Units.ext hA
  exact hp.ne_one (by simpa [this] using horder.symm)

/-- Intersecting congruence kernels of different residue characteristics eliminates torsion. -/
theorem congruence_kernel_inf_torsionFree {L : Type*} [Field L]
    (f : R →+* K) (g : R →+* L) (hchar : ringChar K ≠ ringChar L) :
    IsMulTorsionFree ((Matrix.GeneralLinearGroup.map (n := ι) f).ker ⊓
      (Matrix.GeneralLinearGroup.map (n := ι) g).ker : Subgroup _) := by
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro A hA hfinite
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (show orderOf A ≠ 1 from fun h => hA (orderOf_eq_one_iff.mp h))
  let B := A ^ (orderOf A / p)
  have horderB : orderOf B = p := orderOf_pow_orderOf_div hfinite.orderOf_pos.ne' hpdvd
  have horder : orderOf (B : Matrix.GeneralLinearGroup ι R) = p := by
    rw [Subgroup.orderOf_coe, horderB]
  have hredK : Matrix.GeneralLinearGroup.map f (B : Matrix.GeneralLinearGroup ι R) = 1 := by
    exact MonoidHom.mem_ker.mp B.property.1
  have hredL : Matrix.GeneralLinearGroup.map g (B : Matrix.GeneralLinearGroup ι R) = 1 := by
    exact MonoidHom.mem_ker.mp B.property.2
  have hK : ringChar K = p := congruence_prime_order_characteristic f
    (B : Matrix.GeneralLinearGroup ι R) p hp hredK horder
  have hL : ringChar L = p := congruence_prime_order_characteristic g
    (B : Matrix.GeneralLinearGroup ι R) p hp hredL horder
  exact hchar (hK.trans hL.symm)

/-- Two finite residue fields supply the finite-index normal torsion-free congruence subgroup. -/
theorem exists_finiteIndexNormal_torsionFree_of_finite_residues {L : Type*}
    [Field L] [Finite K] [Finite L] (f : R →+* K) (g : R →+* L)
    (hchar : ringChar K ≠ ringChar L) :
    ∃ H : FiniteIndexNormalSubgroup (Matrix.GeneralLinearGroup ι R),
      IsMulTorsionFree H.toSubgroup := by
  let H : Subgroup (Matrix.GeneralLinearGroup ι R) :=
    (Matrix.GeneralLinearGroup.map f).ker ⊓ (Matrix.GeneralLinearGroup.map g).ker
  exact ⟨FiniteIndexNormalSubgroup.ofSubgroup H,
    congruence_kernel_inf_torsionFree f g hchar⟩

/-- The integer ring is Jacobson, including its nonmaximal zero prime. -/
theorem integer_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro I hI
  have := hI
  by_cases hbot : I = ⊥
  · subst I
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    by_contra hx0
    obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (x.natAbs + 1)
    have : Fact p.Prime := ⟨hp⟩
    have hxmem : x ∈ Ideal.span {(p : ℤ)} :=
      (Ideal.mem_sInf.mp hx) ⟨bot_le, inferInstance⟩
    have hdiv : p ∣ x.natAbs := Int.natCast_dvd.mp (Ideal.mem_span_singleton.mp hxmem)
    have hle : p ≤ x.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hx0) hdiv
    omega
  · have : I.IsMaximal := IsPrime.to_maximal_ideal hbot
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A field of finite type over the integers is finite. -/
theorem finite_field_of_integer_finiteType (k : Type*) [Field k] [Algebra ℤ k]
    [Algebra.FiniteType ℤ k] : Finite k := by
  have : IsJacobsonRing ℤ := integer_isJacobsonRing
  have hfinite := finite_of_finite_type_of_isJacobsonRing ℤ k
  have : Module.Finite ℤ k := by
    convert hfinite using 1
    exact Subsingleton.elim _ _
  have : Algebra.IsIntegral ℤ k := by
    let : Module ℤ k := (inferInstance : Algebra ℤ k).toModule
    exact Algebra.IsIntegral.of_finite ℤ k
  let I : Ideal ℤ := RingHom.ker (algebraMap ℤ k)
  have : I.IsMaximal := Algebra.ker_algebraMap_isMaximal_of_isIntegral ℤ k
  have hI : I ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int I
  have : Finite (ℤ ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let S : Subalgebra ℤ k := (Algebra.ofId ℤ k).range
  have : Finite S := by
    change Finite (algebraMap ℤ k).range
    exact Finite.of_equiv (ℤ ⧸ I)
      (RingHom.quotientKerEquivRange (algebraMap ℤ k)).toEquiv
  have : Module.Finite S k := Module.Finite.of_restrictScalars_finite ℤ S k
  exact Module.finite_of_finite S

/-- A characteristic-zero finite-type integer domain has finite residue fields of different
characteristics. -/
theorem exists_distinct_finite_residues [CharZero R] [Algebra ℤ R] [Algebra.FiniteType ℤ R] :
    ∃ I J : Ideal R, I.IsMaximal ∧ J.IsMaximal ∧ Finite (R ⧸ I) ∧ Finite (R ⧸ J) ∧
      ringChar (R ⧸ I) ≠ ringChar (R ⧸ J) := by
  have : IsJacobsonRing ℤ := integer_isJacobsonRing
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  have : Algebra.FiniteType ℤ (R ⧸ I) := Algebra.FiniteType.trans (R := ℤ) (S := R) inferInstance inferInstance
  have : Finite (R ⧸ I) := finite_field_of_integer_finiteType (R ⧸ I)
  let p := ringChar (R ⧸ I)
  have hp : p ≠ 0 := CharP.ringChar_ne_zero_of_finite (R ⧸ I)
  have hnot : (p : R) ∉ (⊥ : Ideal R).jacobson := by
    rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing R) Ideal.isRadical_bot]
    simpa only [Ideal.mem_bot, Nat.cast_eq_zero] using hp
  have hex : ∃ J : Ideal R, J.IsMaximal ∧ (p : R) ∉ J := by
    by_contra! h
    apply hnot
    exact Ideal.mem_sInf.mpr fun J hJ => h J hJ.2
  obtain ⟨J, hJ, havoid⟩ := hex
  let : Field (R ⧸ J) := Ideal.Quotient.field J
  have : Algebra.FiniteType ℤ (R ⧸ J) := Algebra.FiniteType.trans (R := ℤ) (S := R) inferInstance inferInstance
  have : Finite (R ⧸ J) := finite_field_of_integer_finiteType (R ⧸ J)
  refine ⟨I, J, hI, hJ, inferInstance, inferInstance, ?_⟩
  intro heq
  have hz : (p : R ⧸ J) = 0 := by
    change (ringChar (R ⧸ I) : R ⧸ J) = 0
    rw [heq]
    exact CharP.cast_eq_zero _ _
  exact havoid ((Ideal.Quotient.eq_zero_iff_mem).mp (by simpa using hz))

/-- The congruence construction for a characteristic-zero finite-type integer domain. -/
theorem finiteType_generalLinear_exists_torsionFree [CharZero R] [Algebra ℤ R]
    [Algebra.FiniteType ℤ R] :
    ∃ H : FiniteIndexNormalSubgroup (Matrix.GeneralLinearGroup ι R),
      IsMulTorsionFree H.toSubgroup := by
  obtain ⟨I, J, hI, hJ, hIfin, hJfin, hchar⟩ := exists_distinct_finite_residues (R := R)
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let : Field (R ⧸ J) := Ideal.Quotient.field J
  exact exists_finiteIndexNormal_torsionFree_of_finite_residues
    (Ideal.Quotient.mk I) (Ideal.Quotient.mk J) hchar

/-- The entries of a finitely generated matrix group lie in a finite-type integer subalgebra. -/
theorem finiteType_coefficient_algebra {G : Type*} [Group G] [Group.FG G]
    (ρ : G →* Matrix.GeneralLinearGroup ι K) :
    ∃ S : Subalgebra ℤ K, Algebra.FiniteType ℤ S ∧ ∀ g i j, ρ g i j ∈ S := by
  classical
  have : Monoid.FG G := Group.fg_iff_monoid_fg.mp inferInstance
  obtain ⟨s, hsgen, hsfin⟩ := Monoid.fg_iff.mp (inferInstance : Monoid.FG G)
  have : Finite s := hsfin
  let t : Set K := Set.range fun x : s × ι × ι => ρ x.1.val x.2.1 x.2.2
  have ht : t.Finite := Set.finite_range _
  let S := Algebra.adjoin ℤ t
  refine ⟨S, Algebra.FiniteType.adjoin_of_finite ht, ?_⟩
  intro g
  have hg : g ∈ Submonoid.closure s := by rw [hsgen]; trivial
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      intro i j
      exact Algebra.subset_adjoin ⟨(⟨g, hg⟩, i, j), rfl⟩
  | one =>
      intro i j
      rw [map_one]
      change (1 : Matrix ι ι K) i j ∈ S
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | mul x y hx hy ihx ihy =>
      intro i j
      change ((ρ (x * y) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) i j ∈ S
      rw [map_mul, Matrix.GeneralLinearGroup.coe_mul]
      exact S.sum_mem fun k _ => S.mul_mem (ihx i k) (ihy k j)

/-- Restrict a matrix representation to an integer subalgebra containing its entries. -/
noncomputable def coefficientRepresentation {G : Type*} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup ι K) (S : Subalgebra ℤ K)
    (hcoeff : ∀ g i j, ρ g i j ∈ S) : G →* Matrix.GeneralLinearGroup ι S := by
  let v (g : G) : Matrix ι ι S := fun i j => ⟨ρ g i j, hcoeff g i j⟩
  let F : Matrix ι ι S →+* Matrix ι ι K := (S.val : S →+* K).mapMatrix
  have hv (g : G) : F (v g) = (ρ g : Matrix ι ι K) := rfl
  have hF : Function.Injective F := Matrix.map_injective Subtype.val_injective
  refine
    { toFun := fun g =>
        { val := v g
          inv := v g⁻¹
          val_inv := ?_
          inv_val := ?_ }
      map_one' := ?_
      map_mul' := ?_ }
  · apply hF
    rw [map_mul, map_one, hv, hv, map_inv]
    exact (ρ g).val_inv
  · apply hF
    rw [map_mul, map_one, hv, hv, map_inv]
    exact (ρ g).inv_val
  · apply Units.ext
    apply hF
    change F (v 1) = F 1
    rw [hv, map_one, map_one]
    rfl
  · intro g h
    apply Units.ext
    apply hF
    change F (v (g * h)) = F (v g * v h)
    simp only [map_mul, hv, Matrix.GeneralLinearGroup.coe_mul]

/-- Extending the coefficient representation recovers the original representation. -/
theorem coefficientRepresentation_map {G : Type*} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup ι K) (S : Subalgebra ℤ K)
    (hcoeff : ∀ g i j, ρ g i j ∈ S) (g : G) :
    Matrix.GeneralLinearGroup.map (S.val : S →+* K)
      (coefficientRepresentation ρ S hcoeff g) = ρ g := by
  apply Units.ext
  rfl

/-- Restricting coefficients preserves faithfulness. -/
theorem coefficientRepresentation_injective {G : Type*} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup ι K) (S : Subalgebra ℤ K)
    (hcoeff : ∀ g i j, ρ g i j ∈ S) (hρ : Function.Injective ρ) :
    Function.Injective (coefficientRepresentation ρ S hcoeff) := by
  intro g h hgh
  apply hρ
  simpa only [coefficientRepresentation_map] using
    congrArg (Matrix.GeneralLinearGroup.map (S.val : S →+* K)) hgh

/-- Pull back a torsion-free finite-index normal subgroup through an injective representation. -/
theorem finiteIndexNormal_torsionFree_comap {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (N : FiniteIndexNormalSubgroup H)
    (hN : IsMulTorsionFree N.toSubgroup) :
    IsMulTorsionFree (N.comap f).toSubgroup := by
  let ψ : (N.comap f).toSubgroup →* N.toSubgroup :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : G) (y : G)) }
  have hψ : Function.Injective ψ := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro x hx hfin
  exact not_isOfFinOrder_of_isMulTorsionFree (fun h => hx (hψ (h.trans ψ.map_one.symm)))
    (ψ.isOfFinOrder hfin)

/-- Selberg's lemma for any faithful finite-dimensional representation in characteristic zero. -/
theorem selberg_lemma_linear {G : Type*} [Group G] [Group.FG G] [CharZero K]
    (ρ : G →* Matrix.GeneralLinearGroup ι K) (hρ : Function.Injective ρ) :
    ∃ H : FiniteIndexNormalSubgroup G, IsMulTorsionFree H.toSubgroup := by
  obtain ⟨S, hS, hcoeff⟩ := finiteType_coefficient_algebra ρ
  let φ := coefficientRepresentation ρ S hcoeff
  have hφ : Function.Injective φ := coefficientRepresentation_injective ρ S hcoeff hρ
  obtain ⟨N, hN⟩ := finiteType_generalLinear_exists_torsionFree (R := S) (ι := ι)
  exact ⟨N.comap φ, finiteIndexNormal_torsionFree_comap φ hφ N hN⟩

/--
Selberg's lemma: a finitely generated complex matrix group has a normal
finite-index subgroup with no nonidentity finite-order elements.
-/
theorem selberg_lemma {n : ℕ} (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hG : G.FG) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∀ g : G, g ∈ H → IsOfFinOrder g → g = 1 := by
  have : Group.FG G := (Group.fg_iff_subgroup_fg G).mpr hG
  obtain ⟨H, hH⟩ := selberg_lemma_linear (K := ℂ) (ι := Fin n)
    G.subtype Subtype.val_injective
  refine ⟨H.toSubgroup, inferInstance, inferInstance, ?_⟩
  intro g hg hfin
  let x : H.toSubgroup := ⟨g, hg⟩
  have hx : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, ← Subgroup.orderOf_coe x]
    exact hfin.orderOf_pos
  have hxone : x = 1 := by
    by_contra hne
    exact not_isOfFinOrder_of_isMulTorsionFree hne hx
  exact congrArg Subtype.val hxone

end LowDimensionalTopology.Geometry.DiscreteGroups
