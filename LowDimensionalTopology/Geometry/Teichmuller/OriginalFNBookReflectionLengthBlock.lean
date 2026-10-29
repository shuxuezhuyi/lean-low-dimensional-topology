module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookReflectionFrame
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookDualityBlocks
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNativeReflectionAntiSymplectic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Native book length-length reflection sign at every actual marked point

The actual reflection frame and native anti-symplectic producers supply their
laws. The preceding internal length-duality output supplies TL and TT through
the actual book differential. Real bilinearity then cancels the two cross
terms and gives the negative LL value at the reflected point. No LL block or
final Darboux sum is a premise, and no new Unproved input is installed. The final
assembly must discharge internal duality through the physical-curve producer.
A compatible reflection is given; none is asserted for every surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation GeneralQC TeichmullerSpace GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc) (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J)
    (hJcuffs : ∀ j, J '' range (D₀.cuff j).curve = range (D₀.cuff j).curve)
    (hJpants : ∀ a, J '' (D₀.component a).val = (D₀.component a).val)

local notation "T" => TeichmullerSpace R
local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "F" => (I → ℝ) × (I → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, F)
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  («I» := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)
local notation "rN" => originalNativeTeichmullerReflection R hg hgenus J hJ

variable
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3 * g - 3)), φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (left : Fin (3 * g - 3) → Fin 2)

local notation "Nraw" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "b" => (fun a : I ⊕ I => match a with
  | Sum.inl j => (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : I → ℝ))
  | Sum.inr j => ((0 : I → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))
local notation "L" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nbook
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (b (Sum.inl j))) q)
local notation "V" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nbook
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (b (Sum.inr j))) q)

local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "length" => (fun j : I =>
  markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (OriginalClosedGeodesic.toLoop (D₀.cuff j)))

/-- The SAME given compatible reflection negates the actual book LL block
between q and its actual reflected point, using internal preceding length duality. -/
theorem originalFNBook_length_length_reflection_negates
    (hCompat : Compat)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWP : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hDual : letI := C
      ∀ (a : T) (j : I) (z : TangentSpace RI a),
        omega a ![V j a, z] = mfderiv RI 𝓘(ℝ) (length j) a z) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (q : T) (j k : I), omega (rN q) ![L j (rN q), L k (rN q)] =
      -(omega q ![L j q, L k q]) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only at hDual ⊢
  obtain ⟨n, hL, _hV⟩ := exists_originalFNBookReflection_native_frame
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants
    hU φ Θ hφ hΘ hRigid hRealize left hCompat hGeom
  have hblocks := sameOriginalFN_book_twist_blocks_of_length_duality
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left hCompat hDual
  intro q
  have hanti := originalNativeTeichmullerReflection_antiSymplectic
    R hp hg hgenus hΓ hsmooth J hJ hWP q
  let A := omega (rN q)
  let leftLinear (y : TangentSpace RI (rN q)) : TangentSpace RI (rN q) →ₗ[ℝ] ℝ :=
    A.toAlternatingMap.toMultilinearMap.toLinearMap ![0, y] 0
  let rightLinear (x : TangentSpace RI (rN q)) : TangentSpace RI (rN q) →ₗ[ℝ] ℝ :=
    A.toAlternatingMap.toMultilinearMap.toLinearMap ![x, 0] 1
  have hleftValue (x y : TangentSpace RI (rN q)) : leftLinear y x = A ![x, y] := by
    change A (Function.update ![0, y] 0 x) = A ![x, y]
    exact congrArg A (by funext i; fin_cases i <;> rfl)
  have hrightValue (x y : TangentSpace RI (rN q)) : rightLinear x y = A ![x, y] := by
    change A (Function.update ![x, 0] 1 y) = A ![x, y]
    exact congrArg A (by funext i; fin_cases i <;> rfl)
  have haddLeft (x u y : TangentSpace RI (rN q)) (c : ℝ) :
      A ![x + c • u, y] = A ![x, y] + c * A ![u, y] := by
    calc
      A ![x + c • u, y] = leftLinear y (x + c • u) := (hleftValue _ _).symm
      _ = _ := by
        simp only [map_add, map_smul]
        simp only [hleftValue, smul_eq_mul]
  have haddRight (x y v : TangentSpace RI (rN q)) (c : ℝ) :
      A ![x, y + c • v] = A ![x, y] + c * A ![x, v] := by
    calc
      A ![x, y + c • v] = rightLinear x (y + c • v) := (hrightValue _ _).symm
      _ = _ := by
        simp only [map_add, map_smul]
        simp only [hrightValue, smul_eq_mul]
  have hswap (x y : TangentSpace RI (rN q)) : A ![x, y] = -A ![y, x] := by
    simpa only [ContinuousAlternatingMap.coe_toAlternatingMap,
      Matrix.cons_cons_comp_swap_zero_one] using
      A.toAlternatingMap.map_swap ![y, x] (by decide : (0 : Fin 2) ≠ 1)
  intro j k
  have h := congrArg
    (fun B : TangentSpace RI q [⋀^Fin 2]→L[ℝ] ℝ => B ![L j q, L k q]) hanti
  change omega (rN q) (fun i => mfderiv RI RI rN q (![L j q, L k q] i)) =
    -(omega q ![L j q, L k q]) at h
  have hvec : (fun i : Fin 2 => mfderiv RI RI rN q (![L j q, L k q] i)) =
      ![mfderiv RI RI rN q (L j q), mfderiv RI RI rN q (L k q)] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, hL q j, hL q k, haddLeft, haddRight, haddRight] at h
  have hLT : A ![L j (rN q), V k (rN q)] = -(if k = j then (1 : ℝ) else 0) :=
    (hswap _ _).trans (congrArg Neg.neg (hblocks (rN q) k j).1)
  rw [hLT, (hblocks (rN q) j k).1, (hblocks (rN q) j k).2] at h
  by_cases hjk : j = k
  · subst k
    simp only [mul_zero, add_zero] at h
    linarith
  · have hkj : k ≠ j := Ne.symm hjk
    simp only [ite_eq_right hjk, ite_eq_right hkj, neg_zero, mul_zero, add_zero] at h
    linarith

end LowDimensionalTopology.Geometry.Teichmuller
