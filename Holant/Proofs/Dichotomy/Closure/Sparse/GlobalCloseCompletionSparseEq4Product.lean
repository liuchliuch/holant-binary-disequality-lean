import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseEq4Flip
import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorSupport
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenEOTract

/-! A sparse prime Product row produces scalar equality-four through its actual
EO flip graph, two original labelled copies and two literal-I attachments. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseEq4Product
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Marked.SupportAtlas
open StableCurrentEvenEOTransport
namespace S
export GlobalCloseCompletionProductAncestorSupport (embedded_prime_product_support_pair prime_not_singleton)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩) (d : SparseOutput G P q core literal)

def labels : Labelling d.access.source.shape P.count 1 P.arity where
  vertex v := (d.access.uses v).choose
  vertex_arity v := congrArg Sigma.fst (d.access.uses v).choose_spec
  edge _ := 0

theorem exact : LabelledNetwork.Exact P.table d.access.source (labels G P q core literal d) :=
  fun v => (d.access.uses v).choose_spec

theorem central : Signature.CentralSupport d.access.source.denote := by
  rw [←d.access.outputIdentity]
  intro x hx
  exact d.output_eo G P q core literal x (by omega)

include core literal in
theorem original_support (product : Product (embedded G q)) :
    ∃w : Fin 4 → Bool, q w≠0 ∧ q (fun i => !(w i))≠0 ∧
      ∀x,q x≠0 → x=w ∨ x=fun i => !(w i) := by
  have prime : Prime (⟨4,q⟩ : AnySignature (OI.K G)) := literal ▸ core.prime
  obtain ⟨w,support⟩ := S.embedded_prime_product_support_pair (ClosureSourceRows.embedding G)
    q (by decide) prime product
  have left : q w≠0 := by
    intro zero
    apply S.prime_not_singleton q (by decide) prime (fun i => !(w i))
    intro x hx
    exact (support x hx).resolve_left (fun h => hx (h ▸ zero))
  have right : q (fun i => !(w i))≠0 := by
    intro zero
    apply S.prime_not_singleton q (by decide) prime w
    intro x hx
    exact (support x hx).resolve_right (fun h => hx (h ▸ zero))
  exact ⟨w,left,right,support⟩

theorem xor_complement (x m : Fin 4 → Bool) :
    xorWord (fun i => !(x i)) m=fun i => !(xorWord x m i) := by
  funext i
  dsimp only [xorWord]
  cases x i <;> cases m i <;> rfl

theorem pair (product : Product (embedded G q)) :
    Nonempty (GeneralEODEQProducerCore.Pair d.access.source.denote) := by
  obtain ⟨w,left,right,support⟩ := original_support G P q core literal product
  let u := xorWord w d.mask
  have hu : xorWord u d.mask=w := StableCurrentEvenEOTract.xorWord_involution w d.mask
  have hv : xorWord (fun i => !(u i)) d.mask=fun i => !(w i) := by
    rw [xor_complement,hu]
  have eqn : d.access.source.denote=fun x => q (xorWord x d.mask) :=
    d.access.outputIdentity.symm.trans (d.output_literal G P q core literal)
  refine ⟨⟨u,(fun i => !(u i)),?_,?_,?_,?_⟩⟩
  · rw [eqn]
    change q (xorWord u d.mask)≠0
    rw [hu]
    exact left
  · rw [eqn]
    change q (xorWord (fun i => !(u i)) d.mask)≠0
    rw [hv]
    exact right
  · exact le_of_eq ((GeneralEODEQProducerCore.distance_eq_iff u (fun i => !(u i))).mpr
      (by intro i; cases u i <;> decide)).symm
  · intro x hx _
    rw [eqn] at hx
    rcases support _ hx with h | h
    · left
      have he := congrArg (fun y => xorWord y d.mask) h
      simpa only [StableCurrentEvenEOTract.xorWord_involution] using he
    · right
      have he := congrArg (fun y => xorWord y d.mask) h
      simpa only [StableCurrentEvenEOTract.xorWord_involution,xor_complement] using he

include core literal d in
theorem produce (product : Product (embedded G q)) :
    Nonempty (GlobalCloseCompletionEq4Graph.Output G P) := by
  obtain ⟨p⟩ := pair G P q core literal d product
  let R : GeneralEODEQProducerReduction.Reduced P.table :=
    ⟨d.access.source,labels G P q core literal d,exact G P q core literal d,
      d.access.native,central G P q core literal d,p⟩
  obtain ⟨D⟩ := GeneralEODEQProducerNormalize.produce_reduced P.table R
  exact ⟨GlobalCloseCompletionSparseEq4Flip.produce G P D⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseEq4Product
end
