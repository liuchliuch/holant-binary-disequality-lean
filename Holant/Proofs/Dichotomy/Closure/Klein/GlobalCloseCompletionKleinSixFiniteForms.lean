import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixFiniteData
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMBell
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramNorm

/-! Literal geometry of the four surviving six-port label triples.
Two have a displayed proper I factor. The other two are the genuine H6 core
under explicit original-port permutations, for every retained sign choice. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixFiniteForms
open Holant
namespace D
export GlobalCloseCompletionKleinSixFiniteData (source)
end D
namespace C
export GlobalCloseCompletionKleinGramCertificate (pauli)
end C
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
namespace N
export GlobalCloseCompletionKleinGramNorm (wordIndex)
end N
namespace H
export GlobalCloseCompletionKleinH6RMBell (core E bell theta)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def index6 (x : Fin 6→Bool) : Fin 64 :=
  finProdFinEquiv (N.wordIndex ![x 0,x 1],S.index4 ![x 2,x 3,x 4,x 5])

def coreInteger (x : Fin 6→Bool) : ℤ := ∑k : Fin 4,
  C.pauli k (x 0) (x 1)*C.pauli (H.theta k) (x 2) (x 3)*
    C.pauli (H.theta (H.theta k)) (x 4) (x 5)

def flipData (s : Fin 8) : Fin 6→Fin 6 :=
  ![if s.val.testBit 2 then 1 else 0,if s.val.testBit 2 then 0 else 1,
    if s.val.testBit 1 then 3 else 2,if s.val.testBit 1 then 2 else 3,
    if s.val.testBit 0 then 5 else 4,if s.val.testBit 0 then 4 else 5]

theorem flip_involutive : ∀s i,flipData s (flipData s i)=i := by decide +kernel

def flip (s : Fin 8) : Equiv.Perm (Fin 6) where
  toFun := flipData s
  invFun := flipData s
  left_inv := flip_involutive s
  right_inv := flip_involutive s

def swapBlocks : Equiv.Perm (Fin 6) where
  toFun := ![0,1,4,5,2,3]
  invFun := ![0,1,4,5,2,3]
  left_inv := by decide
  right_inv := by decide

theorem factor_first_integer : ∀s : Fin 8,∀x : Fin 6→Bool,
    D.source 1 2 3 s (index6 x)=
      if x 2=x 3 then D.source 1 2 3 s (index6 ![x 0,x 1,false,false,x 4,x 5]) else 0 := by
  decide +kernel

theorem factor_second_integer : ∀s : Fin 8,∀x : Fin 6→Bool,
    D.source 4 8 12 s (index6 x)=
      if x 4=x 5 then D.source 4 8 12 s (index6 ![x 0,x 1,x 2,x 3,false,false]) else 0 := by
  decide +kernel

theorem h6_first_integer : ∀s : Fin 8,∀x : Fin 6→Bool,
    D.source 11 13 6 s (index6 x)=coreInteger (fun i=>x (flip s i)) := by
  decide +kernel

theorem h6_second_integer : ∀s : Fin 8,∀x : Fin 6→Bool,
    D.source 14 7 9 s (index6 x)=coreInteger (fun i=>x ((flip s).trans swapBlocks i)) := by
  decide +kernel

variable {K : Type*} [Field K]

def tensor (a b c : Fin 48) (s : Fin 8) : Signature K 6 := fun x=>(D.source a b c s (index6 x):K)

theorem pauli_cast (k : Fin 4) (a b : Bool) : (C.pauli k a b:K)=H.E k a b := by
  fin_cases k <;> cases a <;> cases b <;> norm_num [C.pauli,H.E,H.bell]

theorem core_cast (x : Fin 6→Bool) : (coreInteger x:K)=H.core x := by
  simp only [coreInteger,H.core,Int.cast_sum,Int.cast_mul,pauli_cast]

theorem factor_first (s : Fin 8) (x : Fin 6→Bool) :
    tensor (K:=K) 1 2 3 s x=Signature.equality (x 2) (x 3)*
      tensor 1 2 3 s ![x 0,x 1,false,false,x 4,x 5] := by
  unfold tensor
  rw [factor_first_integer]
  by_cases h : x 2=x 3 <;> simp [h,Signature.equality]

theorem factor_second (s : Fin 8) (x : Fin 6→Bool) :
    tensor (K:=K) 4 8 12 s x=Signature.equality (x 4) (x 5)*
      tensor 4 8 12 s ![x 0,x 1,x 2,x 3,false,false] := by
  unfold tensor
  rw [factor_second_integer]
  by_cases h : x 4=x 5 <;> simp [h,Signature.equality]

theorem h6_first (s : Fin 8) : tensor (K:=K) 11 13 6 s=Tensor.reindex (flip s) H.core := by
  funext x
  simp only [tensor,h6_first_integer,core_cast,Tensor.reindex]

theorem h6_second (s : Fin 8) : tensor (K:=K) 14 7 9 s=Tensor.reindex ((flip s).trans swapBlocks) H.core := by
  funext x
  simp only [tensor,h6_second_integer,core_cast,Tensor.reindex]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixFiniteForms
end
