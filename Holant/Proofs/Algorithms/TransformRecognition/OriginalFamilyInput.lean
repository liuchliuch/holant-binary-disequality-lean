import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineDecision


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalFamilyInput
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Input := (i : Fin s) → (Fin (arity i) → Bool) → RootCode

def edgeValue (disequality a b : Bool) : ℚ :=
  if a=b then (if disequality then 0 else 1) else (if disequality then 1 else 0)

def pack (input : Input arity) (disequality : Bool) : OriginalAffineSystem.Input arity :=
  fun k => match (LocalAffineVariableLayout.catalogue arity).get k with
    | ⟨.inl i,x⟩ => input i x
    | ⟨.inr _,x⟩ => RationalRootCode.code (edgeValue disequality (x (0 : Fin 2)) (x (1 : Fin 2)))

noncomputable section
def edge (disequality : Bool) : Kernel AlgebraicComplex :=
  if disequality then Signature.disequality else Signature.equality

def values (G : (i : Fin s) → Signature AlgebraicComplex (arity i)) (disequality : Bool) :
    Fin (OriginalAffineSystem.Entries arity) → AlgebraicComplex :=
  fun k => match (LocalAffineVariableLayout.catalogue arity).get k with
    | ⟨.inl i,x⟩ => G i x
    | ⟨.inr _,x⟩ => edge disequality (x (0 : Fin 2)) (x (1 : Fin 2))

theorem edgeValue_coe (disequality a b : Bool) :
    ((edgeValue disequality a b : ℚ) : AlgebraicComplex)=edge disequality a b := by
  cases disequality <;> cases a <;> cases b <;>
    simp [edgeValue,edge,Signature.equality,Signature.disequality]

theorem sourceVertex_values (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (disequality : Bool) :
    OriginalAffineSystem.sourceVertex arity (values arity G disequality)=G := by
  funext i x
  simp only [OriginalAffineSystem.sourceVertex,OriginalAffineSystem.entryIndex,
    values,LocalAffineVariableLayout.get_address, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem sourceEdge_values (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (disequality : Bool) :
    OriginalAffineSystem.sourceEdge arity (values arity G disequality)=edge disequality := by
  funext a b
  simp only [OriginalAffineSystem.sourceEdge,OriginalAffineSystem.entryIndex,
    values,LocalAffineVariableLayout.get_address, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem pack_represents (input : Input arity)
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (hG : ∀ i x, (input i x).Represents (G i x : ℂ)) (disequality : Bool) :
    ∀ k, (pack arity input disequality k).Represents (values arity G disequality k : ℂ) := by
  intro k
  unfold pack values
  generalize (LocalAffineVariableLayout.catalogue arity).get k = p
  rcases p with ⟨j,x⟩
  cases j with
  | inl i => exact hG i x
  | inr u =>
    change (RationalRootCode.code (edgeValue disequality (x (0 : Fin 2)) (x (1 : Fin 2)))).Represents
      ((edge disequality (x (0 : Fin 2)) (x (1 : Fin 2)) : AlgebraicComplex) : ℂ)
    have h := RationalRootCode.represents (edgeValue disequality (x (0 : Fin 2)) (x (1 : Fin 2)))
    rw [←edgeValue_coe disequality (x (0 : Fin 2)) (x (1 : Fin 2))]
    simpa using h

end

def Valid (input : Input arity) : Prop :=
  ∃ G : (i : Fin s) → Signature AlgebraicComplex (arity i),
    ∀ i x, (input i x).Represents (G i x : ℂ)

theorem pack_valid (input : Input arity) (h : Valid arity input) (disequality : Bool) :
    OriginalAffineDecision.InputValid arity (pack arity input disequality) := by
  obtain ⟨G,hG⟩ := h
  exact ⟨values arity G disequality,pack_represents arity input G hG disequality⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalFamilyInput
