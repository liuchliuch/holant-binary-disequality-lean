import Holant.Certificates.MatchingContractionClosure.SurgerySemantics
import Mathlib.Data.Fintype.EquivFin

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {K : Type*} [Field K] {P Q : Type*}

/-- An actual oriented perfect matching with every original port covered once.
The global coefficient records all closed components. -/
structure Presentation (K P : Type*) where
  edges : ℕ
  ports : (Fin edges × Bool) ≃ P
  matrix : Fin edges → Matrix Bool Bool K
  scalar : K

def Presentation.tensor (M : Presentation K P) : Tensor K P :=
  productValue M.ports M.matrix M.scalar

def Presentation.Valid (G : Set (Binary (K := K))) (M : Presentation K P) : Prop :=
  ∀ e, SafeBinary G (M.matrix e)

def Presentation.ofFinite {E : Type*} [Fintype E] (p : (E × Bool) ≃ P)
    (A : E → Binary (K := K)) (κ : K) : Presentation K P where
  edges := Fintype.card E
  ports := (Equiv.prodCongr (Fintype.equivFin E).symm (Equiv.refl Bool)).trans p
  matrix i := A ((Fintype.equivFin E).symm i)
  scalar := κ

theorem Presentation.ofFinite_tensor {E : Type*} [Fintype E] [DecidableEq E] [DecidableEq P]
    (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K) :
    (Presentation.ofFinite p A κ).tensor=productValue p A κ := by
  funext x
  unfold Presentation.tensor Presentation.ofFinite productValue
  apply congrArg (κ*·)
  exact Equiv.prod_comp (Fintype.equivFin E).symm
    (fun e => A e (x (p (e,false))) (x (p (e,true))))

theorem Presentation.ofFinite_valid {E : Type*} [Fintype E]
    {G : Set (Binary (K := K))} (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (hA : ∀ e, SafeBinary G (A e)) : Presentation.Valid G (Presentation.ofFinite p A κ) := by
  intro e
  exact hA _

/-- The zero branch is explicit. In the product branch every factor is
nonsingular, and the retained global scalar is nonzero. -/
def MatchingOrZero (G : Set (Binary (K := K))) (F : Tensor K P) : Prop :=
  F=0 ∨ ∃ M : Presentation K P, M.Valid G ∧ M.scalar≠0 ∧ F=M.tensor

theorem MatchingOrZero.of_product {E : Type*} [Fintype E] [DecidableEq E] [DecidableEq P]
    {G : Set (Binary (K := K))} (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (hA : ∀ e, SafeBinary G (A e)) : MatchingOrZero G (productValue p A κ) := by
  by_cases hκ : κ=0
  · left
    funext x
    simp [productValue,hκ]
  · exact Or.inr ⟨Presentation.ofFinite p A κ,Presentation.ofFinite_valid p A κ hA,
      hκ,(Presentation.ofFinite_tensor p A κ).symm⟩

def Presentation.reindex (M : Presentation K P) (e : P ≃ Q) : Presentation K Q where
  edges := M.edges
  ports := M.ports.trans e
  matrix := M.matrix
  scalar := M.scalar

theorem Presentation.reindex_tensor (M : Presentation K P) (e : P ≃ Q) :
    (M.reindex e).tensor=Tensor.reindex e M.tensor := rfl

theorem MatchingOrZero.reindex {G : Set (Binary (K := K))} {F : Tensor K P}
    (hF : MatchingOrZero G F) (e : P ≃ Q) : MatchingOrZero G (Tensor.reindex e F) := by
  rcases hF with rfl | ⟨M,hM,hκ,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨M.reindex e,hM,hκ,(M.reindex_tensor e).symm⟩

end
end Holant.Certificates.MatchingContractionClosure
