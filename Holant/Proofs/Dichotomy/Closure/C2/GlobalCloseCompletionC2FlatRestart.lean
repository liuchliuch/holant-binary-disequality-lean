import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2PrimeFlatDescent
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatNonzero
import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedFlatLeaf
import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedPredicateRestart

/-! Genuine current-palette restart for every nonflat even prime above arity
four. The actual smaller graph is installed with its complete factor tree,
real group preparation is run, all old rows survive, and the retained nonflat
prime minimum strictly decreases. No successor classification is a premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatRestart
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace F
export GlobalCloseCompletionRetainedFlatLeaf (Predicate split_closed)
end F
namespace R
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end R
namespace S
export GlobalCloseCompletionRetainedPredicateRestart (finalPalette retains_old root_saved output_retained minimum_exists minimum_strict)
end S
namespace M
export GlobalCloseCompletionC2RMActual (rm)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (old : R.Minimum G P (F.Predicate G))

structure Output where
  signature : AnySignature (OI.K G)
  nonzero : signature.2≠0
  positive : 0<signature.1
  actual : Gadget.Realizes P.family .disequality signature.2
  bad : ¬F.Predicate G signature
  smaller : signature.1<old.signature.1

variable (D : Output G P old)

abbrev palette := S.finalPalette G P D.signature D.nonzero D.positive D.actual

def minimum : R.Minimum G (palette G P old D) (F.Predicate G) :=
  (S.minimum_exists G P D.signature D.nonzero D.positive D.actual (F.Predicate G) (F.split_closed G) D.bad).some

theorem minimum_decreases : (minimum G P old D).signature.1<old.signature.1 :=
  S.minimum_strict G P D.signature D.nonzero D.positive D.actual (F.Predicate G) (F.split_closed G) D.bad
    old (minimum G P old D) D.smaller

theorem retains_old : P.family⊆(palette G P old D).family :=
  S.retains_old G P D.signature D.nonzero D.positive D.actual

theorem root_retained : D.signature∈(palette G P old D).family :=
  S.output_retained G P D.signature D.nonzero D.positive D.actual

variable (torsion : ResidualTorsion P.family) (hI : RetainsIdentity P.family)
variable (cardTwo : Nat.card (completeGroup P.family torsion)=2)
variable (c : OI.K G) (hc : c≠0) (rmActual : Gadget.Realizes P.family .disequality (c • M.rm))

include torsion hI cardTwo hc rmActual in
theorem produce {m : ℕ} (f : Signature (OI.K G) (m+2)) (literal : old.signature=⟨m+2,f⟩)
    (six : 6≤m+2) (even : Even (m+2)) : Nonempty (Output G P old) := by
  have retained : (⟨m+2,f⟩ : AnySignature (OI.K G))∈P.family := literal ▸ old.retained
  have prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) := literal ▸ old.prime
  have bad : ¬F.Predicate G ⟨m+2,f⟩ := literal ▸ old.bad
  obtain ⟨n,q,smaller,actualQ,badQ⟩ := GlobalCloseCompletionC2PrimeFlatDescent.smaller
    P.family torsion hI cardTwo (ClosureSourceRows.embedding G) c hc rmActual f
      (Gadget.realizes_of_mem P.family .disequality f retained) prime six even bad
  have nonzero := GlobalCloseCompletionC2FlatNonzero.nonzero (ClosurePhysicalBridge.complexEmbedding G) q badQ
  have positive := GlobalCloseCompletionC2FlatNonzero.positive (ClosurePhysicalBridge.complexEmbedding G) q badQ
  refine ⟨⟨⟨n,q⟩,nonzero,positive,actualQ,badQ,?_⟩⟩
  simpa only [literal] using smaller


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatRestart
end
