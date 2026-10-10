import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffinePhaseFaceSource
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6GateAlgebra

/-! An actual H6 phase probe has a zero and a live coefficient in one physical
parity sector. This is the precise failure consumed by the RM norm source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseUnequal
open Holant Holant.Tractable Holant.Algebraic Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionKleinHigherNonaffinePhasePorts
open GlobalCloseCompletionKleinHigherNonaffinePhaseFaceSource
open scoped BigOperators
namespace A
export GlobalCloseCompletionKleinH6GateAlgebra (action append front_append tail_append sum_three)
end A
namespace D
export GlobalCloseCompletionKleinH6GateData (matrix_cast join)
end D
namespace H
export GlobalCloseCompletionKleinH6RMBell (core E bell theta)
end H
namespace W
export GlobalCloseCompletionKleinHigherNonaffineWalsh (triple six sign output witness)
end W
namespace N
export GlobalCloseCompletionKleinHigherNonaffineFullParity (Normal)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n : ℕ}

theorem action_block (f : Signature K (n+3)) (d a b : Bool) (rest : Word n) :
    A.action false f (append (W.triple d a b) rest)=
      ∑u : Bool,∑v : Bool,H.core (W.six d a b u v)*f (append (W.triple d u v) rest) := by
  change A.action false f (A.append (W.triple d a b) rest)=_
  simp only [A.action,A.front_append,A.tail_append,D.matrix_cast,Bool.false_eq_true,ite_false]
  rw [A.sum_three]
  cases d <;> cases a <;> cases b <;>
    simp [Fintype.sum_bool,H.core,H.E,H.bell,H.theta,Fin.sum_univ_succ,D.join,W.six,W.triple] <;> rfl

theorem action_values (f : Signature K (n+3)) (d : Bool) (rest : Word n)
    (scalar : K) (signs : Bool→Bool→Bool)
    (values : ∀a b,f (append (W.triple d a b) rest)=scalar*W.sign (signs a b)) (a b : Bool) :
    A.action false f (append (W.triple d a b) rest)=scalar*W.output d signs a b := by
  rw [action_block]
  simp only [values,W.output,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

def Unequal {m : ℕ} (f : Signature K m) : Prop :=
  ∃x y,ClosureSixPort.parity x=ClosureSixPort.parity y ∧ f x=0 ∧ f y≠0

theorem scale_unequal {m : ℕ} (f : Signature K m) (c : K) (nonzero : c≠0)
    (unequal : Unequal f) : Unequal (c • f) := by
  obtain ⟨x,y,parity,zero,live⟩ := unequal
  exact ⟨x,y,parity,by change c*f x=0;rw [zero,mul_zero],mul_ne_zero nonzero live⟩

variable [CharZero K]
theorem face_unequal (f : Signature K (n+3)) (d : Bool) (rest : Word n)
    (scalar : K) (nonzero : scalar≠0) (signs : Bool→Bool→Bool)
    (values : ∀a b,f (append (W.triple d a b) rest)=scalar*W.sign (signs a b))
    (even : W.sign (K:=K) (signs false false)*W.sign (signs true true)=
      W.sign (signs false true)*W.sign (signs true false)) : Unequal (A.action false f) := by
  obtain ⟨a,b,a',b',zero,live⟩ := W.witness d signs even
  refine ⟨append (W.triple d a b) rest,append (W.triple d a' b') rest,?_,?_,?_⟩
  · rw [parity_triple,parity_triple]
  · rw [action_values f d rest scalar signs values,zero,mul_zero]
  · rw [action_values f d rest scalar signs values]
    exact mul_ne_zero nonzero live

variable {s : ℕ} {ar : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (ar i.val))
local instance : NumberField (OI.K G) := OI.numberField G

theorem source (f : Signature (OI.K G) (n+3)) (normal : N.Normal G f)
    (bad : ¬GlobalCloseCompletionKleinAffineLeaf.IsAffine G ⟨n+3,f⟩) :
    ∃p : Equiv.Perm (Fin (n+3)),Unequal (A.action false (reorder p f)) := by
  obtain ⟨p,d,rest,signs,values,even⟩ :=
    GlobalCloseCompletionKleinHigherNonaffinePhaseFaceSource.source G f normal bad
  exact ⟨p,face_unequal _ d rest normal.scalar normal.nonzero signs values even⟩

theorem not_uniform {m : ℕ} (f : Signature (OI.K G) m) (unequal : Unequal f) :
    ¬GlobalCloseCompletionKleinHigherNonaffineNormSource.UniformSquares G f := by
  intro uniform
  obtain ⟨x,y,parity,zero,live⟩ := unequal
  have h := uniform (Holant.ReedMuller.FlatNetwork.vectorWord x)
    (Holant.ReedMuller.FlatNetwork.vectorWord y) (by
      rwa [GlobalCloseCompletionKleinHigherNonaffineFullParity.parity_dot,
        GlobalCloseCompletionKleinHigherNonaffineFullParity.parity_dot])
  simp only [Holant.ReedMuller.FlatNetwork.word_vector] at h
  rw [zero,map_zero,zero_pow (by decide : 2≠0)] at h
  have nonzero : ClosurePhysicalBridge.complexEmbedding G (f y)≠0 := (map_ne_zero _).mpr live
  exact (pow_ne_zero 2 nonzero) h.symm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseUnequal
end
