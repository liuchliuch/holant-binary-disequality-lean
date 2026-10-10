import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineNormSource
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineParitySource

/-! The RM norm source's surviving case is exact full-parity support, with
one original-field nonzero coefficient and Boolean signs. Uniform coefficient
squares and pure support parity jointly derive both directions of support. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFullParity
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open GlobalCloseCompletionProductAncestorParity
namespace N
export GlobalCloseCompletionKleinHigherNonaffineNormSource (UniformSquares complexEmbedding)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
open scoped BigOperators

theorem parity_dot {n : ℕ} (x : Fin n→Bool) :
    dot (ones n) (vectorWord x)=ClosureSixPort.parity x := by
  simp only [dot,ones,Pi.one_apply,one_mul,ClosureSixPort.parity]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x i <;> simp [vectorWord,ClosureSixPort.bit,h,boolEquiv]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure Normal {n : ℕ} (f : Signature (OI.K G) n) where
  scalar : OI.K G
  nonzero : scalar≠0
  parity : ZMod 2
  phase : (Fin n→Bool)→Bool
  value : ∀x,f x=if ClosureSixPort.parity x=parity then scalar*(if phase x then -1 else 1) else 0

 theorem normal {n : ℕ} (f : Signature (OI.K G) n) (live : f≠0)
    (pure : PureParity f) (uniform : N.UniformSquares G f) : Nonempty (Normal G f) := by
  classical
  obtain ⟨x0,hx0⟩ : ∃x0,f x0≠0 := by by_contra! none;exact live (funext none)
  let phase : (Fin n→Bool)→Bool := fun x=>decide (f x≠f x0)
  refine ⟨⟨f x0,hx0,ClosureSixPort.parity x0,phase,?_⟩⟩
  intro x
  by_cases same : ClosureSixPort.parity x=ClosureSixPort.parity x0
  · rw [if_pos same]
    have squared : f x^2=f x0^2 := by
      apply (N.complexEmbedding G).injective
      rw [map_pow,map_pow]
      have h := uniform (vectorWord x) (vectorWord x0) (by rwa [parity_dot,parity_dot])
      simpa only [word_vector] using h
    by_cases equal : f x=f x0
    · simp [phase,equal]
    · have opposite := (sq_eq_sq_iff_eq_or_eq_neg.mp squared).resolve_left equal
      simp [phase,equal,opposite]
  · rw [if_neg same]
    by_contra hx
    exact same (pure x x0 hx hx0)

 theorem support_iff {n : ℕ} (f : Signature (OI.K G) n) (M : Normal G f) (x : Fin n→Bool) :
    f x≠0 ↔ ClosureSixPort.parity x=M.parity := by
  rw [M.value]
  by_cases same : ClosureSixPort.parity x=M.parity
  · simp only [same,ite_true,iff_true]
    exact mul_ne_zero M.nonzero (by split_ifs <;> norm_num)
  · simp [same]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFullParity
end
