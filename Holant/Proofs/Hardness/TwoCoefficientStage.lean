import Holant.Proofs.Hardness.TwoCoefficientSignatures
import Holant.Proofs.Hardness.ExactTwoChainTemplate

/-! The genuine ordered two-copy escape gadget. Each stage wires a previous
network to a port-permuted second copy using exactly two native X edges.
Depth0/1/2 therefore contains1/2/4 ORIGINAL q vertices. Its coefficient map
is derived from the actual contraction, not supplied as a transformation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientStage
open Holant
namespace C
export ExactTwoChain (series series_denote)
end C
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R
namespace S
export TwoCoefficientSignatures (weighted middleSwap swapped_table)
end S
namespace D
export TwoCoefficientData (step stage)
end D
open Holant.LocalDrafts.Hardness.EightVertexNonexception
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

/-- Ordinary same-pair series law, also used by the weighted interpolation
chain. Both actual local networks are retained. -/
theorem series_weighted (N M : Network K 4) (a b c d : K)
    (hN : N.denote=S.weighted a b) (hM : M.denote=S.weighted c d) :
    (C.series N M).denote=S.weighted (a*c) (2*b*d) := by
  funext x
  rw [C.series_denote,hN,hM]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.weighted,table,Fintype.sum_bool,h0,h1,h2,h3] <;> ring

/-- Exact ordered two-copy law: the second copy swaps ports1/2 before the
same two actual contractions. -/
theorem series_swapped (N M : Network K 4) (a b : K)
    (hN : N.denote=S.weighted a b) (hM : M.denote=S.weighted a b) :
    (C.series N (R.reindex M S.middleSwap)).denote=S.weighted (a*b) (b*(a+b)) := by
  funext x
  rw [C.series_denote,R.reindex_denote,hN,hM,S.swapped_table]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.weighted,table,Fintype.sum_bool,h0,h1,h2,h3] <;> ring

def network (a b : K) : ℕ → Network K 4
  | 0=>Network.corolla (S.weighted a b)
  | k+1=>C.series (network a b k) (R.reindex (network a b k) S.middleSwap)

theorem denote (a b : K) (k : ℕ) :
    (network a b k).denote=S.weighted (D.stage a b k).1 (D.stage a b k).2 := by
  induction k with
  | zero=>exact Network.denote_corolla _
  | succ k ih=>exact series_swapped _ _ _ _ ih ih

theorem signature (a b : K) (k : ℕ) (v : Fin (network a b k).shape.vertices) :
    (⟨(network a b k).shape.arity v,(network a b k).vertex v⟩ : AnySignature K)=⟨4,S.weighted a b⟩ := by
  induction k with
  | zero=>rfl
  | succ k ih=>
      change (⟨(Network.tensorFinite (network a b k) (R.reindex (network a b k) S.middleSwap)).arity
          (finSumFinEquiv.symm v),
        (Network.tensorFinite (network a b k) (R.reindex (network a b k) S.middleSwap)).vertex
          (finSumFinEquiv.symm v)⟩ : AnySignature K)=_
      cases finSumFinEquiv.symm v with
      | inl v=>exact ih v
      | inr v=>exact ih v

theorem arity (a b : K) (k : ℕ) (v : Fin (network a b k).shape.vertices) :
    (network a b k).shape.arity v=4 := congrArg Sigma.fst (signature a b k v)

theorem native (a b : K) (k : ℕ) : ∀e,(network a b k).edge e=Signature.disequality := by
  induction k with
  | zero=>intro e; exact Fin.elim0 e
  | succ k ih=>
      intro e
      refine Fin.cases rfl (fun e=>?_) e
      refine Fin.cases rfl (fun e=>?_) e
      change Sum.elim (network a b k).edge (network a b k).edge (finSumFinEquiv.symm e)=_
      cases finSumFinEquiv.symm e with
      | inl e=>exact ih e
      | inr e=>exact ih e

theorem counts (a b : K) (k : ℕ) :
    (network a b k).shape.vertices=2^k ∧ (network a b k).shape.edges+2=2^(k+1) := by
  induction k with
  | zero=>constructor <;> rfl
  | succ k ih=>
      change (network a b k).shape.vertices+(network a b k).shape.vertices=2^(k+1) ∧
        ((network a b k).shape.edges+(network a b k).shape.edges+1)+1+2=2^(k+1+1)
      rw [pow_succ,pow_succ]
      omega

theorem bounded_counts (a b : K) (k : ℕ) (hk : k≤2) :
    (network a b k).shape.vertices≤4 ∧ (network a b k).shape.edges≤6 := by
  have hv := Nat.pow_le_pow_right (by decide : 0<2) hk
  have he := Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_right hk 1)
  have h := counts a b k
  norm_num at hv he
  omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientStage
