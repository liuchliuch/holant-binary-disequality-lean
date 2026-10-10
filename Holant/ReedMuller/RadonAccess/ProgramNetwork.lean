import Holant.ReedMuller.FlatNetwork.GenerationNetworkProgram
import Holant.ReedMuller.FlatNetwork.GenerationNative

/-! Actual coordinate circuits act on any supplied signature, retaining one
original corolla and adding only the literal RM vertices specified by a program.
This is the physical operator used for accessible Radon cards. -/
namespace Holant.ReedMuller.RadonAccess
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open GenerationNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem denote_applyGate_word (N : Network ℂ n) (g : GenerationGate n) (x : Fin n → Bool) :
    (applyGate N g).denote x=N.denote (wordVector (g.inverse.applyWord (vectorWord x))) := by
  cases g with
  | tau s hs => exact denote_attachRM N s hs x
  | perm e =>
    rw [applyGate,denote_reindex]
    change N.denote (fun i => x (e i))=N.denote (wordVector ((GenerationGate.perm e).inverse.applyWord (vectorWord x)))
    apply congrArg N.denote
    funext i
    exact (boolEquiv.symm_apply_apply (x (e i))).symm

theorem denote_realize_word (p : GenerationProgram n) (N : Network ℂ n) (x : Fin n → Bool) :
    (realize p N).denote x=N.denote (wordVector (p.inverse.word (vectorWord x))) := by
  induction p generalizing x with
  | nil => simpa only [realize,GenerationProgram.inverse_nil,GenerationProgram.word,word_vector]
  | cons g p ih =>
    rw [realize,denote_applyGate_word,ih,vector_word]
    rw [GenerationProgram.inverse_cons,GenerationProgram.word_append]
    rfl

def Uses {m : ℕ} (F : SignatureFamily ℂ) (N : Network ℂ m) : Prop :=
  ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈F

def EdgesIX {m : ℕ} (N : Network ℂ m) : Prop :=
  ∀ e,N.edge e=Signature.equality ∨ N.edge e=Signature.disequality

theorem uses_applyGate (F : SignatureFamily ℂ) (N : Network ℂ n) (g : GenerationGate n)
    (hN : Uses F N) (hRM : (⟨8,rmCore⟩ : AnySignature ℂ)∈F) : Uses F (applyGate N g) := by
  cases g with
  | perm e => exact hN
  | tau s hs =>
    intro v
    change (⟨_,(attachFinite N rmCore (supportSelection s hs) rmOrder).vertex
      ((Fintype.equivFin (Fin N.shape.vertices ⊕ Unit)).symm v)⟩ : AnySignature ℂ)∈F
    cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Unit)).symm v with
    | inl v => exact hN v
    | inr u => exact hRM

theorem edges_applyGate (N : Network ℂ n) (g : GenerationGate n) (hN : EdgesIX N) :
    EdgesIX (applyGate N g) := by
  cases g with
  | perm e => exact hN
  | tau s hs =>
    have h : ∀ e,(attachFinite N rmCore (supportSelection s hs) rmOrder).edge e=Signature.equality ∨
        (attachFinite N rmCore (supportSelection s hs) rmOrder).edge e=Signature.disequality := by
      rintro (e|i)
      · exact hN e
      · exact Or.inl rfl
    exact fun e => h ((Fintype.equivFin (Fin N.shape.edges ⊕ Fin 4)).symm e)

theorem uses_realize (F : SignatureFamily ℂ) (p : GenerationProgram n) (N : Network ℂ n)
    (hN : Uses F N) (hRM : (⟨8,rmCore⟩ : AnySignature ℂ)∈F) : Uses F (realize p N) := by
  induction p with
  | nil => exact hN
  | cons g p ih => exact uses_applyGate F _ g ih hRM

theorem edges_realize (p : GenerationProgram n) (N : Network ℂ n) (hN : EdgesIX N) :
    EdgesIX (realize p N) := by
  induction p with
  | nil => exact hN
  | cons g p ih => exact edges_applyGate _ g ih

/-- Its syntax contains exactly one original corolla, with one RM attachment
for each weight-four gate and boundary relabeling for each permutation. -/
def oneCopy (p : GenerationProgram n) (g : Signature ℂ n) : Network ℂ n :=
  realize p (Network.corolla g)

theorem oneCopy_denote (p : GenerationProgram n) (g : Signature ℂ n) (x : Fin n → Bool) :
    (oneCopy p g).denote x=g (wordVector (p.inverse.word (vectorWord x))) := by
  rw [oneCopy,denote_realize_word,Network.denote_corolla]

theorem oneCopy_uses (F : SignatureFamily ℂ) (p : GenerationProgram n) (g : Signature ℂ n)
    (hg : (⟨n,g⟩ : AnySignature ℂ)∈F) (hRM : (⟨8,rmCore⟩ : AnySignature ℂ)∈F) : Uses F (oneCopy p g) :=
  uses_realize F p _ (fun _ => hg) hRM

theorem oneCopy_edges (p : GenerationProgram n) (g : Signature ℂ n) : EdgesIX (oneCopy p g) :=
  edges_realize p _ (fun e => Fin.elim0 e)

theorem oneCopy_vertices (p : GenerationProgram n) (g : Signature ℂ n) :
    (oneCopy p g).shape.vertices≤1+p.length := realize_vertices p _
theorem oneCopy_edge_bound (p : GenerationProgram n) (g : Signature ℂ n) :
    (oneCopy p g).shape.edges≤4*p.length := by
  change (realize p (Network.corolla g)).shape.edges≤4*p.length
  have H := realize_edges p (Network.corolla g)
  change (realize p (Network.corolla g)).shape.edges≤0+4*p.length at H
  simpa only [Nat.zero_add] using H

end
end Holant.ReedMuller.RadonAccess
