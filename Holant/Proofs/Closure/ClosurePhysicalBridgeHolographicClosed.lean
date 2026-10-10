import Holant.Proofs.Closure.ClosurePhysicalBridgeNetwork
import Holant.Holographic

/-! The narrow CLOSED inverse holographic adapter, reusing the frozen actual
network transformation and scalar denotation theorem. The transformed edge is
mandatory and has the exact inverse-basis orientation. This theorem is n=0;
open q4 graphs need the separate free-port boundary-action adapter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.FinitePGL2.Stabilization

/-- Edge pullbacks compose in the forward matrix order. -/
theorem pullback_comp {K : Type} [CommSemiring K] (E M N : Kernel K) :
    Kernel.pullback (Kernel.pullback E M) N = Kernel.pullback E (Kernel.mul M N) := by
  unfold Kernel.pullback
  rw [Kernel.transpose_mul]
  simp only [Kernel.mul_assoc]

theorem pullback_inverse {K : Type} [CommSemiring K] (E M N : Kernel K)
    (hMN : Kernel.mul M N = Signature.equality) :
    Kernel.pullback (Kernel.pullback E M) N = E := by
  rw [pullback_comp,hMN]
  simp [Kernel.pullback]

/-- Literal familyAction membership gives inverse-action membership in the
actual source family. There is no independent availability assumption. -/
theorem inverse_family_label (B : InvertibleKernel) (F : SignatureFamily AlgebraicComplex)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ familyAction B F) :
    (⟨n,B.symm.action f⟩ : AnySignature AlgebraicComplex) ∈ F := by
  rcases hf with ⟨⟨m,g⟩,hg,he⟩
  change (⟨m,B.action g⟩ : AnySignature AlgebraicComplex) = ⟨n,f⟩ at he
  cases he
  simpa using hg

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (B : InvertibleKernel) (N : Network AlgebraicComplex 0)
variable (labels : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex) ∈
  familyAction B (RH.mapFamily (algebraicEmbedding G) P.family))
variable (edges : ∀ e, N.edge e = Kernel.pullback Signature.disequality B.inverse)

def restoredClosed : Network AlgebraicComplex 0 :=
  Network.holographicTransform N B.matrix B.inverse

include labels in
theorem restoredClosed_labels (v : Fin N.shape.vertices) :
    (⟨(restoredClosed B N).shape.arity v,(restoredClosed B N).vertex v⟩ : AnySignature AlgebraicComplex) ∈
      RH.mapFamily (algebraicEmbedding G) P.family :=
  inverse_family_label B _ (N.vertex v) (labels v)

include edges in
theorem restoredClosed_native (e : Fin N.shape.edges) :
    (restoredClosed B N).edge e = Signature.disequality := by
  change Kernel.pullback (N.edge e) B.matrix = Signature.disequality
  rw [edges e]
  exact pullback_inverse _ _ _ B.inverse_matrix

theorem restoredClosed_denote : (restoredClosed B N).denote = N.denote :=
  Network.denote_holographicTransform N B.matrix B.inverse B.matrix_inverse

structure HolographicClosedAccess where
  restored : Network AlgebraicComplex 0
  restoredIdentity : restored = restoredClosed B N
  sameShape : restored.shape = N.shape
  labels : ∀ v, (⟨restored.shape.arity v,restored.vertex v⟩ : AnySignature AlgebraicComplex) ∈
    RH.mapFamily (algebraicEmbedding G) P.family
  native : ∀ e, restored.edge e = Signature.disequality
  scalarIdentity : restored.denote = N.denote
  access : NetworkGraphAccess G P (algebraicEmbedding G) restored labels
  accessIdentity : access = fromNetwork G P (algebraicEmbedding G) restored labels native
  mappedOutput : RH.mapSignature (algebraicEmbedding G) access.output = N.denote

/-- Actual basis, exact changed edges and real changed vertex labels are the
whole input. Restored native source availability and both charged programmes
are derived internally. Closed-only scalar invariance is used only at n=0. -/
def fromHolographicClosed : HolographicClosedAccess G P B N := by
  let D := restoredClosed B N
  let d := fromNetwork G P (algebraicEmbedding G) D
    (restoredClosed_labels G P B N labels) (restoredClosed_native B N edges)
  exact ⟨D,rfl,rfl,restoredClosed_labels G P B N labels,restoredClosed_native B N edges,
    restoredClosed_denote B N,d,rfl,d.mappedOutput.trans (restoredClosed_denote B N)⟩

abbrev HolographicClosedAccess.output (d : HolographicClosedAccess G P B N) := d.access.output
abbrev HolographicClosedAccess.toOriginal (d : HolographicClosedAccess G P B N) := d.access.toOriginal
abbrev HolographicClosedAccess.fromOriginal (d : HolographicClosedAccess G P B N) := d.access.fromOriginal
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
