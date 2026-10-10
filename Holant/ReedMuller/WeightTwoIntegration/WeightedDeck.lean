import Holant.ReedMuller.MatchingConsistency.Deck

/-! Full coefficient data of the actual weighted equality cards. Units retain
every original nonzero scalar and diagonal factor, rather than just support. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.FixedCoreDeck Holant.ReedMuller.CoefficientAtlas
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
variable {ι κ K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

 structure WeightedProduct (K ι : Type*) [Field K] where
  edges : ℕ
  ports : (Fin edges × Bool) ≃ ι
  diagonal : Fin edges → Bool → Kˣ
  scalar : Kˣ

 def WeightedProduct.value (P : WeightedProduct K ι) : Tensor K ι := fun x =>
  (P.scalar:K)*∏e,if x (P.ports (e,false))=x (P.ports (e,true)) then (P.diagonal e (x (P.ports (e,false))):K) else 0

 def WeightedProduct.diagonalValue (P : WeightedProduct K ι) (x : ι → Bool) : Kˣ :=
  P.scalar*∏e,P.diagonal e (x (P.ports (e,false)))

 theorem WeightedProduct.value_nonzero_iff (P : WeightedProduct K ι) (x : ι → Bool) :
    P.value x≠0 ↔ ∀e,x (P.ports (e,false))=x (P.ports (e,true)) := by
  simp only [WeightedProduct.value,Fintype.prod_ite_zero]
  split_ifs with h
  · exact iff_of_true (mul_ne_zero P.scalar.ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun e _ => (P.diagonal e _).ne_zero))) h
  · simp [h]

 theorem WeightedProduct.value_eq_diagonal (P : WeightedProduct K ι) (x : ι → Bool)
    (hx : P.value x≠0) : P.value x=(P.diagonalValue x:K) := by
  have he := (P.value_nonzero_iff x).mp hx
  simp only [WeightedProduct.value,he,ite_true,WeightedProduct.diagonalValue,Units.val_mul,Units.coe_prod]

 def WeightedProduct.reindex (P : WeightedProduct K ι) (e : ι ≃ κ) : WeightedProduct K κ :=
  ⟨P.edges,P.ports.trans e,P.diagonal,P.scalar⟩

 theorem WeightedProduct.reindex_value (P : WeightedProduct K ι) (e : ι ≃ κ) :
    (P.reindex e).value=Tensor.reindex e P.value := rfl

 def WeightedProduct.scale (P : WeightedProduct K ι) (c : Kˣ) : WeightedProduct K ι :=
  ⟨P.edges,P.ports,P.diagonal,c*P.scalar⟩

 theorem WeightedProduct.scale_value (P : WeightedProduct K ι) (c : Kˣ) :
    (P.scale c).value=(c:K) • P.value := by
  funext x
  simp only [WeightedProduct.scale,WeightedProduct.value,Units.val_mul,Pi.smul_apply,smul_eq_mul]
  exact mul_assoc _ _ _

 def ProductOrZero (f : Tensor K ι) : Prop := f=0 ∨ ∃P : WeightedProduct K ι,f=P.value

 theorem ProductOrZero.reindex {f : Tensor K ι} (h : ProductOrZero f) (e : ι ≃ κ) :
    ProductOrZero (Tensor.reindex e f) := by
  rcases h with rfl | ⟨P,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨P.reindex e,rfl⟩

 theorem ProductOrZero.of_smul {f : Tensor K ι} (c : K) (hc : c≠0) (h : ProductOrZero (c • f)) :
    ProductOrZero f := by
  rcases h with h | ⟨P,hP⟩
  · left
    funext x
    exact (mul_eq_zero.mp (congrFun h x)).resolve_left hc
  · right
    refine ⟨P.scale (Units.mk0 c hc)⁻¹,?_⟩
    rw [WeightedProduct.scale_value,←hP,smul_smul]
    simp [hc]

 def WeightedDeck [DecidableEq ι] (f : Tensor K ι) : Prop :=
   ∀i j : ι,i≠j → ∀minus : Bool,ProductOrZero (card f i j minus)

 def ofWalshMatching {n r : ℕ} (M : WeightedMatching n r) : WeightedProduct ℂ (Fin n) :=
  ⟨r,M.ports,(fun e b => Units.mk0 (M.diagonal e b) (M.diagonal_ne_zero e b)),
    Units.mk0 M.scalar M.scalar_ne_zero⟩

 theorem ofWalshMatching_value {n r : ℕ} (M : WeightedMatching n r) :
    (ofWalshMatching M).value=M.value := rfl

 theorem actual_weighted_deck {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2)) (hd : ActualMatchingDeck G R f) :
    WeightedDeck (walsh f) := by
  intro i j hij minus
  have hh : ProductOrZero (walsh (representativeCard R f (Dihedral.CompatibleClosure.pairOrder i j) minus)) := by
    rcases walsh_matchingOrZero hG hspan (hd _ minus) with h | ⟨r,M,hM⟩
    · exact Or.inl h
    · exact Or.inr ⟨ofWalshMatching M,hM.symm⟩
  rw [representativeCard_exact,walsh_smul,walsh_physical_card] at hh
  have he := ProductOrZero.of_smul (R.scale minus) (R.scale_ne_zero minus) hh
  rw [card_named_ordered _ i j hij minus]
  exact he.reindex (residualOrder i j hij)

end Holant.ReedMuller.WeightTwoIntegration
