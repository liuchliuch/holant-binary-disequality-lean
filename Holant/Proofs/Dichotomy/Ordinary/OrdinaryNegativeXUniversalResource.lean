import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPrivateComposeCore
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockResourcesXOriginal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXMinimalWitnesses

/-! Common concrete interface for internally supplied one-, three-, and
seven-port resources. A resource is an actual original-table private recipe
with checked odd boundary/even interior incidence, never a free trace label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalResource
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeMixedBlockData
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
export OrdinaryNegativeSparseMixingSource (Block)
end M
namespace A
export OrdinaryNegativeSparseMixingAlpha
  (codeThree codeSeven codeThree_affine codeSeven_affine phaseOne_not_affine
   phaseThree_not_affine phaseSeven_not_affine twist)
end A
namespace B
export OrdinaryNegativeOcticCommonBasis (basis)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

inductive Kind where
  | one
  | three
  | seven
  deriving DecidableEq

def Kind.arity : Kind→ℕ | .one=>1 | .three=>3 | .seven=>7
def Kind.rank : Kind→ℕ | .one=>1 | .three=>2 | .seven=>3

def Kind.code : (k : Kind)→Word k.rank→Word k.arity
  | .one=>fun x=>x
  | .three=>A.codeThree
  | .seven=>A.codeSeven

theorem Kind.code_affine (k : Kind) : TwoTranslate.IsAffineMap k.code := by
  cases k
  · exact coordinates_isAffineMap id
  · exact A.codeThree_affine
  · exact A.codeSeven_affine

theorem Kind.phase_bad (k : Kind) : ¬Affine (fun x=>A.twist (k.code x)) := by
  cases k
  · exact A.phaseOne_not_affine
  · exact A.phaseThree_not_affine
  · exact A.phaseSeven_not_affine

structure OddResource {s : ℕ} (b : ℕ→ℕ) (n : ℕ) where
  privateCount : ℕ
  rows : Recipe (u:=1) (s:=s) (a:=fun _=>n+privateCount) (b:=b)
  constant_even : ∀q : Bool,Even ((ports rows 0).count (.inl q))
  boundary_odd : ∀i : Fin n,Odd ((ports rows 0).count (.inr (Fin.castAdd privateCount i)))
  private_even : ∀i : Fin privateCount,Even ((ports rows 0).count (.inr (Fin.natAdd n i)))

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val))

def OddResource.signature {n : ℕ} (R : OddResource (s:=s) b n) : Signature K n :=
  M.trace H R.privateCount R.rows 0

def OddResource.ambient {n : ℕ} (R : OddResource (s:=s) b n) : Signature AlgebraicComplex n :=
  fun x=>(R.signature H x : AlgebraicComplex)

structure AlphaResource (kind : Kind) extends OddResource (s:=s) b kind.arity where
  alpha : Affine ((B.basis true).symm.action (toOddResource.ambient H))
  full : ∀x,toOddResource.ambient H (kind.code x)≠0

structure AffineResource (kind : Kind) extends OddResource (s:=s) b kind.arity where
  affine : Affine (toOddResource.ambient H)
  full : ∀x,toOddResource.ambient H (kind.code x)≠0

/-- The even alternative is already an actual table recipe and its literal
nonaffine private-sum row, with no support-closure premise. -/
def EvenBad : Prop := ∃n : ℕ,∃R : M.Block (s:=s) (b:=b) n,
  ¬Affine (fun x=>(R.signature H x : AlgebraicComplex))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalResource
end
