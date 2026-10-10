import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralModels
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralLiteralDeck

/-! Coefficient extraction from the preserved marked-octahedral proof. The same ordered q4 contraction and its right-X
transfer map. Only the group-independent Frobenius/card identities are
consumed from FourPortPreparation; neither tetrahedral direction tests nor
its preserver classification are applied to the octahedral group. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open scoped BigOperators Matrix

abbrev PortOrder := Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.PortOrder
abbrev rawCard := Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.rawCard
abbrev relabel := Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.relabel
abbrev blockSwap := Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.blockSwap

/-- Typed inverse receipts for the original coefficient chart. The old
lemmas are stated with quaternionCoefficient, not the coordinates wrapper. -/
private theorem assemble_coordinates (B : BinaryMatrix) : assemble (coordinates B) = B := by
  change assemble (quaternionCoefficient B) = B
  exact assemble_coefficient B

private theorem coordinates_assemble (v : V) : coordinates (assemble v) = v := by
  change quaternionCoefficient (assemble v) = v
  exact coefficient_assemble v

/-- Both spellings have literally the same four native-X coefficients. -/
private theorem nativeX_marked :
    (Holant.Certificates.MatchingContractionClosure.X : BinaryMatrix) =
      Matrix.of Holant.Certificates.MatchingProductBridge.X := rfl

private theorem direction_nativeX (f : Form) :
    Direction f (Holant.Certificates.MatchingContractionClosure.X : BinaryMatrix) := by
  rw [nativeX_marked]
  exact direction_X f

/-- Transport the same ordered card through the actual reindex composition. -/
private theorem rawCard_relabel (q : FourTensor) (e d : PortOrder) (K : BinaryMatrix) :
    rawCard (relabel e q) d K = rawCard q (d.trans e) K := by
  change Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.rawCard
      (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.relabel e q) d K =
    Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.rawCard q (d.trans e) K
  unfold Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.rawCard
  rw [Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.relabel_relabel]

private theorem relabel_trans (q : FourTensor) (e d : PortOrder) :
    relabel (d.trans e) q = relabel d (relabel e q) :=
  (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.relabel_relabel q e d).symm

def kernel (f : Form) (k : Fin 24) : BinaryMatrix :=
  complexMatrix (theta f (OctahedralSeparator.standard k))
def point (f : Form) (k : Fin 24) : V := coordinates (kernel f k)
def Roots (f : Form) : Set V := CoefficientSet {K | Direction f K}
def Safe (f : Form) (B : BinaryMatrix) : Prop := B = 0 ∨ Direction f B
def VectorSafe (f : Form) (v : V) : Prop := v = 0 ∨ v ∈ Roots f
def LiteralDeck (f : Form) (q : FourTensor) : Prop :=
  ∀ e : PortOrder, ∀ K : BinaryMatrix, Direction f K → Safe f (rawCard q e K)

theorem point_mem (f : Form) (k : Fin 24) : point f k ∈ Roots f :=
  ⟨kernel f k,Direction.standard f k,rfl⟩

theorem roots_iff (f : Form) (v : V) : v ∈ Roots f ↔
    ∃ k : Fin 24, ∃ c : ℂ, c ≠ 0 ∧ v = c • point f k := by
  rw [Roots,mem_coefficientSet_iff]
  constructor
  · rintro ⟨c,hc,k,he⟩
    refine ⟨k,c,hc,?_⟩
    have hh := congrArg coordinates he
    change quaternionCoefficient (assemble v) = coordinates (c • kernel f k) at hh
    simpa only [coefficient_assemble,map_smul,point] using hh
  · rintro ⟨k,c,hc,rfl⟩
    refine ⟨c,hc,k,?_⟩
    change coordinates.symm (c • coordinates (kernel f k)) = c • kernel f k
    simp

theorem roots_saturated (f : Form) : Saturated (Roots f) := by
  intro v hv c hc
  obtain ⟨k,d,hd,rfl⟩ := (roots_iff f v).mp hv
  exact (roots_iff f _).mpr ⟨k,c*d,mul_ne_zero hc hd,by rw [smul_smul]⟩

theorem point_ne_zero (f : Form) (k : Fin 24) : point f k ≠ 0 := by
  intro hz
  have he : kernel f k = 0 := coordinates.injective (hz.trans (map_zero coordinates).symm)
  have hd := Direction.det_ne_zero (Direction.standard f k)
  change Matrix.det (kernel f k) ≠ 0 at hd
  apply hd
  rw [he]
  simp

theorem safe_scale (f : Form) (c : ℂ) (hc : c ≠ 0) (B : BinaryMatrix) :
    Safe f (c • B) ↔ Safe f B := by
  constructor
  · rintro (hz | hs)
    · exact Or.inl ((smul_eq_zero.mp hz).resolve_left hc)
    · have hh := hs.smul (inv_ne_zero hc)
      exact Or.inr (by simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh)
  · rintro (rfl | hs)
    · exact Or.inl (smul_zero _)
    · exact Or.inr (hs.smul hc)

theorem safe_coordinates (f : Form) (B : BinaryMatrix) :
    VectorSafe f (coordinates B) ↔ Safe f B := by
  constructor
  · rintro (hz | hs)
    · exact Or.inl (coordinates.injective (hz.trans (map_zero coordinates).symm))
    · have hh : Direction f (assemble (coordinates B)) :=
        (mem_coefficientSet_iff {K | Direction f K} (coordinates B)).mp hs
      rw [assemble_coordinates] at hh
      exact Or.inr hh
  · rintro (rfl | hs)
    · exact Or.inl (map_zero coordinates)
    · exact Or.inr ⟨B,hs,rfl⟩

/-- This is an actual multiplication by the literal native X. -/
theorem safe_rightX (f : Form) (B : BinaryMatrix) :
    Safe f (B*Holant.Certificates.MatchingContractionClosure.X) ↔ Safe f B := by
  constructor
  · rintro (hz | hs)
    · have hh := congrArg (fun M : BinaryMatrix =>
        M*Holant.Certificates.MatchingContractionClosure.X) hz
      exact Or.inl (by simpa only [Matrix.mul_assoc,
        Holant.Certificates.MatchingContractionClosure.X_mul_X,
        Matrix.mul_one,Matrix.zero_mul] using hh)
    · have hh := direction_mul hs (direction_nativeX f)
      exact Or.inr (by simpa only [Matrix.mul_assoc,
        Holant.Certificates.MatchingContractionClosure.X_mul_X,Matrix.mul_one] using hh)
  · rintro (rfl | hs)
    · exact Or.inl (Matrix.zero_mul _)
    · exact Or.inr (direction_mul hs (direction_nativeX f))

theorem deck_relabel (f : Form) (q : FourTensor) (h : LiteralDeck f q) (e : PortOrder) :
    LiteralDeck f (relabel e q) := by
  intro d K hK
  rw [rawCard_relabel]
  exact h (d.trans e) K hK

theorem card_action (q : FourTensor) (e : PortOrder) (K : BinaryMatrix) :
    cardMatrix (relabel e q) *ᵥ coordinates K = coordinates (rawCard q e K) := by
  have hh : cardMatrix (relabel e q) *ᵥ coordinates K =
      coordinates (rawCard (relabel e q) (Equiv.refl _) K) :=
    Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.cardMatrix_action
      (relabel e q) K
  have he : rawCard (relabel e q) (Equiv.refl _) K = rawCard q e K := by
    rw [rawCard_relabel, Equiv.refl_trans]
  exact hh.trans (congrArg coordinates he)

theorem deck_oneSided (f : Form) (q : FourTensor) (h : LiteralDeck f q) :
    OneSided (Roots f) (cardMatrix q) := by
  intro v hv
  have hK : Direction f (assemble v) := (mem_coefficientSet_iff _ v).mp hv
  have ha : cardMatrix q *ᵥ v = coordinates (rawCard q (Equiv.refl _) (assemble v)) := by
    have hh : cardMatrix q *ᵥ coordinates (assemble v) =
        coordinates (rawCard q (Equiv.refl _) (assemble v)) :=
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.cardMatrix_action
        q (assemble v)
    rw [coordinates_assemble] at hh
    exact hh
  rw [ha]
  exact (safe_coordinates f _).mpr (h (Equiv.refl _) (assemble v) hK)

theorem deck_twoSided (f : Form) (q : FourTensor) (h : LiteralDeck f q) :
    TwoSided (Roots f) (cardMatrix q) := by
  refine ⟨deck_oneSided f q h,?_⟩
  rw [←Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.cardMatrix_complement]
  exact deck_oneSided f _ (deck_relabel f q h blockSwap)

/-- All 24 original port permutations, not an unoriented pair flag. -/
theorem deck_iff_twoSided_all_orders (f : Form) (q : FourTensor) :
    LiteralDeck f q ↔ ∀ e : PortOrder, TwoSided (Roots f) (cardMatrix (relabel e q)) := by
  constructor
  · intro h e
    exact deck_twoSided f _ (deck_relabel f q h e)
  · intro h e K hK
    have hv : coordinates K ∈ Roots f := ⟨K,hK,rfl⟩
    have hh := (h e).1 _ hv
    rw [card_action] at hh
    exact (safe_coordinates f _).mp hh

/-- Coordinate matrix of right multiplication by the actual X. -/
def rightX : End := sandwich 1 Holant.Certificates.MatchingContractionClosure.X

theorem rightX_action (v : V) : rightX *ᵥ v =
    coordinates (assemble v*Holant.Certificates.MatchingContractionClosure.X) := by
  simpa only [rightX,Matrix.one_mul] using sandwich_action 1
    Holant.Certificates.MatchingContractionClosure.X v

theorem rightX_square : rightX*rightX = 1 := by
  apply matrix_ext_action
  intro v
  rw [←Matrix.mulVec_mulVec,rightX_action,rightX_action,Matrix.one_mulVec]
  change coordinates (assemble (quaternionCoefficient
    (assemble v*Holant.Certificates.MatchingContractionClosure.X))*
      Holant.Certificates.MatchingContractionClosure.X) = v
  rw [assemble_coefficient,Matrix.mul_assoc,
    Holant.Certificates.MatchingContractionClosure.X_mul_X,Matrix.mul_one]
  exact coefficient_assemble v

theorem rightX_sharp : sharp rightX = rightX := by
  ext i j
  rw [sharp_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rightX,sandwich,coordinates_apply,quaternionCoefficient,quaternionBasis,
      Q0,Q1,Q2,Q3,Signature.equality,frobeniusSigns,Matrix.mul_apply,
      Matrix.one_apply,Holant.Certificates.MatchingContractionClosure.X,Signature.disequality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem rightX_twoSided (f : Form) : TwoSided (Roots f) rightX := by
  have h : OneSided (Roots f) rightX := by
    intro v hv
    have hK : Direction f (assemble v) := (mem_coefficientSet_iff _ v).mp hv
    rw [rightX_action]
    exact (safe_coordinates f _).mpr (Or.inr (direction_mul hK (direction_nativeX f)))
  exact ⟨h,by simpa only [rightX_sharp] using h⟩

/-- This matrix acts by Phi(q,e)(K) X, in the same original coordinates. -/
def transferMatrix (q : FourTensor) (e : PortOrder) : End :=
  rightX*cardMatrix (relabel e q)

theorem transfer_action (q : FourTensor) (e : PortOrder) (K : BinaryMatrix) :
    transferMatrix q e *ᵥ coordinates K =
      coordinates (rawCard q e K*Holant.Certificates.MatchingContractionClosure.X) := by
  rw [transferMatrix,←Matrix.mulVec_mulVec,card_action,rightX_action]
  change coordinates (assemble (quaternionCoefficient (rawCard q e K))*_) = _
  rw [assemble_coefficient]

/-- The complementary map has both literal right-X factors. -/
theorem transfer_complement (q : FourTensor) (e : PortOrder) :
    transferMatrix q (blockSwap.trans e) =
      rightX*sharp (transferMatrix q e)*rightX := by
  unfold transferMatrix
  rw [relabel_trans]
  have he : cardMatrix (relabel blockSwap (relabel e q)) =
      sharp (cardMatrix (relabel e q)) :=
    Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.cardMatrix_complement
      (relabel e q)
  rw [he,sharp_mul,rightX_sharp]
  simp only [Matrix.mul_assoc,rightX_square,Matrix.mul_one]

theorem transfer_twoSided_iff (f : Form) (q : FourTensor) (e : PortOrder) :
    TwoSided (Roots f) (transferMatrix q e) ↔
      TwoSided (Roots f) (cardMatrix (relabel e q)) := by
  constructor
  · intro h
    have hh := twoSided_comp (rightX_twoSided f) h
    simpa only [transferMatrix,←Matrix.mul_assoc,rightX_square,Matrix.one_mul] using hh
  · intro h
    exact twoSided_comp (rightX_twoSided f) h

theorem deck_iff_transfer_all_orders (f : Form) (q : FourTensor) :
    LiteralDeck f q ↔ ∀ e : PortOrder, TwoSided (Roots f) (transferMatrix q e) := by
  rw [deck_iff_twoSided_all_orders]
  exact forall_congr' (fun e => (transfer_twoSided_iff f q e).symm)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
