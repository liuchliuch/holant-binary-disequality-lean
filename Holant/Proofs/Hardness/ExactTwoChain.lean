import Holant.Proofs.Hardness.ExactTwoSignatures
import Holant.Proofs.Hardness.DenseEOUnitLocal
import Holant.Proofs.Hardness.SparseUnitNative

/-!
# Actual positive EXACT2 chains with a two-edge interface

Each successor appends one original EXACT2 corolla and joins the old ordered
ports1,3 to its ports0,2 by two native-X edges. No binary surrogate
is an original vertex. With k extra copies the actual network has k+1 original
vertices and2k edges. The actual ordered boundary grouping(0,2)|(1,3) gives E+2^k B,
where E is precisely{0101,1010}. E at parameter0 is an interpolation target,
not a falsely claimed fixed local q/X realization.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChain
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote)
end Chain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

export ExactTwoSignatures (q E B spectral spectral_linear E_reference q_self_dual)

def joinOrder : Equiv.Perm (Fin 8) where
  toFun := ![4,0,6,2,1,5,3,7]
  invFun := ![1,4,3,6,0,5,2,7]
  left_inv := by decide
  right_inv := by decide

def series (N M : Network K 4) : Network K 4 :=
  ((Chain.reindex (Chain.tensor N M) joinOrder).contract Signature.disequality).contract Signature.disequality

theorem series_denote (N M : Network K 4) (x : Fin 4 → Bool) :
    (series N M).denote x=
      ∑u : Bool,∑v : Bool,N.denote ![x 0,u,x 2,v]*M.denote ![!u,x 1,!v,x 3] := by
  rw [series,Network.denote_contract,Network.denote_contract,Chain.reindex_denote,Chain.tensor_denote]
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  have hl (a b c d : Bool) :
      (fun i : Fin 4=>(Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))) : Fin 8 → Bool)
        (joinOrder (Fin.castAdd 4 i)))=![x 0,a,x 2,c] := by
    funext i
    fin_cases i <;> rfl
  have hr (a b c d : Bool) :
      (fun i : Fin 4=>(Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))) : Fin 8 → Bool)
        (joinOrder (Fin.natAdd 4 i)))=![b,x 1,d,x 3] := by
    funext i
    fin_cases i <;> rfl
  simp only [hl,hr,Fintype.sum_bool,Bool.not_false,Bool.not_true]
  ring

theorem series_spectral (N : Network K 4) (t : K) (hN : N.denote=spectral t) :
    (series N (Network.corolla q)).denote=spectral (2*t) := by
  funext x
  rw [series_denote,Network.denote_corolla,hN]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [q,spectral,table,Fintype.sum_bool,h0,h1,h2,h3] <;> ring

def network : ℕ → Network K 4
  | 0=>Network.corolla q
  | k+1=>series (network k) (Network.corolla q)

theorem network_denote (k : ℕ) : (network (K:=K) k).denote=spectral ((2 : K)^k) := by
  induction k with
  | zero=>simp [network,Network.denote_corolla,q,spectral]
  | succ k ih=>
      rw [network,series_spectral _ _ ih,pow_succ]
      congr 1
      ring

abbrev crossed (k : ℕ) : Network K 4 := network k

theorem crossed_denote (k : ℕ) : (crossed (K:=K) k).denote=spectral ((2 : K)^k) := network_denote k

theorem crossed_pencil (k : ℕ) : (crossed (K:=K) k).denote=E+(2 : K)^k • B := by
  rw [crossed_denote,spectral_linear]

theorem network_counts (k : ℕ) :
    (network (K:=K) k).shape.vertices=k+1 ∧ (network (K:=K) k).shape.edges=2*k := by
  induction k with
  | zero=>constructor <;> rfl
  | succ k ih=>
      change (network (K:=K) k).shape.vertices+1=k+1+1 ∧
        ((network (K:=K) k).shape.edges+0+1)+1=2*(k+1)
      omega

theorem crossed_counts (k : ℕ) :
    (crossed (K:=K) k).shape.vertices=k+1 ∧ (crossed (K:=K) k).shape.edges=2*k := network_counts k

/-- These are the exact nodes used by the existing geometric arithmetic
programme: k=i+1 extra copies, so every query is a positive chain. -/
theorem nodes_injective [CharZero K] (m : ℕ) :
    Function.Injective (fun i : Fin (m+1)=>(2 : K)^(i.val+1)) :=
  Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.doubling_nodes_injective m

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChain
