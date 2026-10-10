import Holant.Proofs.Hardness.ThreeModeChain

/-! Actual positive-length blocks for finite-size spectral separation. Every
vertex is the original q(a,b,c). The boundary exchange is physical reindexing,
not an extra oracle signature. No scalar nonresonance claim is made here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStage
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export ThreeModeSignatures (original spectral original_spectral)
end S
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end Chain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

def A (a b : K) (n : ℕ) : K := ((a+b)^n-(b-a)^n)/2
def B (a b : K) (n : ℕ) : K := ((a+b)^n+(b-a)^n)/2
def C (c : K) (n : ℕ) : K := c^n

/-- Exchanges the 0011/1100 and 0101/1010 complementary pairs. -/
def swapAC : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv := by decide
  right_inv := by decide

theorem swapAC_original (a b c : K) :
    Tensor.reindex swapAC (S.original a b c)=S.original c b a := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex_apply,swapAC,S.original,table,h0,h1,h2,h3]

/-- n is required positive by the semantic and resource theorems. -/
def rawStage (a b c : K) (n : ℕ) : Network K 4 :=
  ThreeModeChain.network a b c (n-1)

def stage (a b c : K) (n : ℕ) : Network K 4 :=
  Chain.reindex (rawStage a b c n) swapAC

theorem rawStage_denote [CharZero K] (a b c : K) (n : ℕ) (hn : 0<n) :
    (rawStage a b c n).denote=S.original (A a b n) (B a b n) (C c n) := by
  rw [rawStage,ThreeModeChain.network_denote,Nat.sub_add_cancel (by omega : 1≤n)]
  rfl

theorem stage_table [CharZero K] (a b c : K) (n : ℕ) (hn : 0<n) :
    (stage a b c n).denote=S.original (C c n) (B a b n) (A a b n) := by
  rw [stage,Chain.reindex_denote,rawStage_denote a b c n hn,swapAC_original]

theorem stage_denote [CharZero K] (a b c : K) (n : ℕ) (hn : 0<n) :
    (stage a b c n).denote=S.spectral (A a b n)
      (B a b n+C c n) (B a b n-C c n) := by
  rw [stage_table a b c n hn,S.original_spectral,add_comm (C c n)]

theorem stage_counts (a b c : K) (n : ℕ) (hn : 0<n) :
    (stage a b c n).shape.vertices=n ∧ (stage a b c n).shape.edges=2*n-2 := by
  change (rawStage a b c n).shape.vertices=n ∧ (rawStage a b c n).shape.edges=2*n-2
  have h := ThreeModeChain.counts a b c (n-1)
  unfold rawStage
  omega

theorem stage_signature (a b c : K) (n : ℕ)
    (j : Fin (stage a b c n).shape.vertices) :
    (⟨(stage a b c n).shape.arity j,(stage a b c n).vertex j⟩ : AnySignature K)=
      ⟨4,S.original a b c⟩ := ThreeModeChain.signature a b c (n-1) j

theorem stage_native (a b c : K) (n : ℕ) :
    ∀e,(stage a b c n).edge e=Signature.disequality :=
  ThreeModeChain.native a b c (n-1)

/-- A chain of k+1 fully expanded n-copy blocks, with original q rows only. -/
def blockChain (a b c : K) (n : ℕ) : ℕ → Network K 4
  | 0 => stage a b c n
  | k+1 => ExactTwoChain.series (blockChain a b c n k) (stage a b c n)

theorem blockChain_denote [CharZero K] (a b c : K) (n : ℕ) (hn : 0<n) (k : ℕ) :
    (blockChain a b c n k).denote=S.spectral ((A a b n)^(k+1))
      ((B a b n+C c n)^(k+1)) ((B a b n-C c n)^(k+1)) := by
  induction k with
  | zero => simpa [blockChain] using stage_denote a b c n hn
  | succ k ih =>
      rw [blockChain,ThreeModeChain.series_spectral _ _ _ _ _ _ _ _ ih
        (stage_denote a b c n hn)]
      simp only [pow_succ]

theorem blockChain_counts (a b c : K) (n : ℕ) (hn : 0<n) (k : ℕ) :
    (blockChain a b c n k).shape.vertices=n*(k+1) ∧
      (blockChain a b c n k).shape.edges=2*n*(k+1)-2 := by
  induction k with
  | zero => simpa [blockChain] using stage_counts a b c n hn
  | succ k ih =>
      change (blockChain a b c n k).shape.vertices+(stage a b c n).shape.vertices=n*(k+1+1) ∧
        ((blockChain a b c n k).shape.edges+(stage a b c n).shape.edges+1)+1=2*n*(k+1+1)-2
      rw [ih.1,ih.2,(stage_counts a b c n hn).1,(stage_counts a b c n hn).2]
      constructor
      · simp [Nat.mul_add]
      · simp only [Nat.mul_add, Nat.mul_one]
        omega

theorem blockChain_signature (a b c : K) (n k : ℕ)
    (j : Fin (blockChain a b c n k).shape.vertices) :
    (⟨(blockChain a b c n k).shape.arity j,(blockChain a b c n k).vertex j⟩ : AnySignature K)=
      ⟨4,S.original a b c⟩ := by
  induction k with
  | zero => exact stage_signature a b c n j
  | succ k ih =>
      change (⟨(Network.tensorFinite (blockChain a b c n k) (stage a b c n)).arity (finSumFinEquiv.symm j),
        (Network.tensorFinite (blockChain a b c n k) (stage a b c n)).vertex (finSumFinEquiv.symm j)⟩ : AnySignature K)=_
      cases finSumFinEquiv.symm j with
      | inl j => exact ih j
      | inr j => exact stage_signature a b c n j

theorem blockChain_arity (a b c : K) (n k : ℕ)
    (j : Fin (blockChain a b c n k).shape.vertices) :
    (blockChain a b c n k).shape.arity j=4 :=
  congrArg Sigma.fst (blockChain_signature a b c n k j)

theorem blockChain_native (a b c : K) (n k : ℕ) :
    ∀e,(blockChain a b c n k).edge e=Signature.disequality := by
  induction k with
  | zero => exact stage_native a b c n
  | succ k ih =>
      intro e
      refine Fin.cases rfl (fun e=>?_) e
      refine Fin.cases rfl (fun e=>?_) e
      change Sum.elim (blockChain a b c n k).edge (stage a b c n).edge (finSumFinEquiv.symm e)=_
      cases finSumFinEquiv.symm e with
      | inl e => exact ih e
      | inr e => exact stage_native a b c n e

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStage
