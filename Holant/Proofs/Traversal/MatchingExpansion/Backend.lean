import Holant.Proofs.Traversal.MatchingExpansion.Compiler
import Holant.Proofs.Algorithms.OneHotSource
import Holant.Proofs.Algorithms.OriginalFamily


namespace Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Backend
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
noncomputable section

variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
    (opposite : Bool) (hf : ∀ i, SourceTensorClosure (matchingImage opposite) (G i))

def edges (_ : Fin 1) : Kernel AlgebraicComplex := Signature.disequality
abbrev coefficient := OriginalFamily.coefficient (Templates.signatures G opposite hf) edges
abbrev algebraic := OriginalFamily.coefficient_algebraic (Templates.signatures G opposite hf) edges
abbrev presentation := OriginalFamily.presentation (Templates.signatures G opposite hf) edges
abbrev tables := OriginalFamily.tables (Templates.signatures G opposite hf) edges
abbrev value := OriginalFamily.value (Templates.signatures G opposite hf) edges

theorem vertex_decode (i : Fin (Templates.size G opposite hf))
    (x : Fin (Templates.arity G opposite hf i.val) → Bool) :
    ((presentation G opposite hf).decode ((tables G opposite hf).vertex i x) : AlgebraicComplex) =
      Templates.signatures G opposite hf i x :=
  familyCoordinates_spec (coefficient G opposite hf) (algebraic G opposite hf) (.inl ⟨i,x⟩)

theorem edge_decode (i : Fin 1) (u v : Bool) :
    ((presentation G opposite hf).decode ((tables G opposite hf).edge i u v) : AlgebraicComplex) =
      Signature.disequality u v :=
  familyCoordinates_spec (coefficient G opposite hf) (algebraic G opposite hf) (.inr (i,u,v))

theorem vertex_oneHot (i : Fin (Templates.size G opposite hf)) :
    Signature.OneHot (fun x => (presentation G opposite hf).decode ((tables G opposite hf).vertex i x)) := by
  intro x hx
  apply Subtype.ext
  change ((presentation G opposite hf).decode ((tables G opposite hf).vertex i x) : AlgebraicComplex) = 0
  rw [vertex_decode]
  exact Templates.oneHot G opposite hf i x hx

theorem edge_native (i : Fin 1) (u v : Bool) :
    (presentation G opposite hf).decode ((tables G opposite hf).edge i u v) = Signature.disequality u v := by
  apply Subtype.ext
  rw [edge_decode]
  cases u <;> cases v <;> rfl

def computes : Computes (Compiler.outputEncoding G opposite hf) (presentation G opposite hf).encoding
    (value G opposite hf) :=
  OneHotSource.computes (presentation G opposite hf) (tables G opposite hf)
    (vertex_oneHot G opposite hf) (edge_native G opposite hf)

theorem value_exact (r : Compiler.Output G opposite hf) :
    (value G opposite hf r : AlgebraicComplex) =
      (r.val.realize r.property (Templates.signatures G opposite hf) edges).denote Fin.elim0 :=
  OriginalFamily.value_exact _ _ r

end
end Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Backend
