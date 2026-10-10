import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBUnary
import Holant.Proofs.Closure.ClosureFactorTreeAction
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! Transport the SAME saved singular factor tree analytically. Its actual
retained unary has one supported bit after B normalization. No coordinate
matrix is installed as a gadget and no new palette group is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNormalizedPin
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace U
export GlobalCloseCompletionBUnary (root root_nonzero palette)
end U
namespace Pn
export EightVertexGaugePinAccess (scaledPin both_actual)
export EightVertexGaugePinLeaf (SingleSupport leaf_support binary_support unary_formula)
end Pn
namespace A
export ClosureFactorTreeAction (signature tree leaves)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem singular_leaf {L : Type} [Field L] (f : Signature L 2)
    (tree : FactorTree (⟨2,f⟩ : AnySignature L)) (singular : Matrix.det (binaryMatrix f)=0) :
    ∃g : AnySignature L,g∈tree.leaves ∧ g.1=1 := by
  cases tree with
  | leaf f prime =>
    have hp : Prime (⟨2,Holant.Projective.BoundedTorsion.binarySignature (binaryMatrix f)⟩ : AnySignature L) := by
      simpa only [binarySignature_binaryMatrix] using prime
    exact False.elim ((prime_binary_nonsingular _ hp) singular)
  | @split f a b split left right =>
    have ha : a.1=1 := by
      have harity := split.arity
      have hleft := split.left_pos
      have hright := split.right_pos
      change a.1+b.1=2 at harity
      omega
    cases left with
    | leaf a prime => exact ⟨a,Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self a)),ha⟩
    | split nested left right =>
      have := nested.arity
      have := nested.left_pos
      have := nested.right_pos
      omega

private theorem normalized_leaf {L : Type} [Field L] (phi : L→+*AlgebraicComplex)
    (B : InvertibleKernel) {f : AnySignature L} (tree : FactorTree f)
    (single : Pn.SingleSupport (B.action (RingHomRealization.mapSignature phi f.2)))
    (g : AnySignature L) (member : g∈tree.leaves) :
    Pn.SingleSupport (B.action (RingHomRealization.mapSignature phi g.2)) := by
  induction tree with
  | leaf f prime =>
    have same : g=f := Multiset.mem_singleton.mp member
    subst g
    exact single
  | split split left right ihl ihr =>
    rcases Multiset.mem_add.mp member with hl|hr
    · exact ihl (EightVertexGaugePinLeaf.split_left (ClosureFactorTreeAction.split B (split.map phi)) single) hl
    · exact ihr (EightVertexGaugePinLeaf.split_right (ClosureFactorTreeAction.split B (split.map phi)) single) hr

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (r : GlobalCloseCompletionBDenseEscape.SingularReceipt G P)

abbrev normalized {n : ℕ} (f : Signature (OI.K G) n) : Signature AlgebraicComplex n :=
  basisB.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)

private theorem root_single : Pn.SingleSupport (normalized G (U.root G P r).2) := by
  have form : normalized G (U.root G P r).2=kernelSignature (scale r.coefficient r.normalized) := by
    change basisB.symm.action (kernelSignature (r.original.map (ClosureSourceRows.embedding G)))=_
    rw [transport_signature,r.normalization]
  rw [form]
  apply Pn.binary_support
  obtain ⟨i,j,live,zero⟩ := r.oneHot G P
  refine ⟨i,j,mul_ne_zero r.coefficient_nonzero live,?_⟩
  intro b d gap
  simp only [scale,zero b d gap,mul_zero]

structure Receipt : Type 1 where
  label : Fin (U.palette G P r).count
  output : Signature (OI.K G) 1
  literal : (⟨(U.palette G P r).arity label.val,(U.palette G P r).table label⟩ : AnySignature (OI.K G))=⟨1,output⟩
  retained : (⟨1,output⟩ : AnySignature (OI.K G))∈(U.palette G P r).family
  access : CurrentSignatureAccess G (U.palette G P r) ⟨1,output⟩
  bit : Bool
  coefficient : AlgebraicComplex
  nonzero : coefficient≠0
  exact : normalized G output=Pn.scaledPin bit coefficient

theorem exists_receipt : Nonempty (Receipt G P r) := by
  let tree := RetainedFactorCatalogue.tree G (U.root G P r) (U.root_nonzero G P r)
  have singular : Matrix.det (binaryMatrix (binarySignature r.original))=0 := r.singular
  obtain ⟨g,hg,hg1⟩ := singular_leaf _ tree singular
  let Q := U.palette G P r
  let rootLabel := RetainedFactorCatalogue.rootLabel G P (U.root G P r) (U.root_nonzero G P r)
  have saved : (⟨⟨Q.arity rootLabel.val,Q.table rootLabel⟩,Q.trees rootLabel⟩ : TreeOccurrence (OI.K G))=
      ⟨U.root G P r,tree⟩ :=
    ProgrammeSaturation.root_saved G P (U.root G P r) (U.root_nonzero G P r) (by change 0<2; decide) r.actual
  have leaves := congrArg (fun z : TreeOccurrence (OI.K G)=>z.2.leaves) saved
  have hgQ : g∈(Q.trees rootLabel).leaves := by
    change (Q.trees rootLabel).leaves=tree.leaves at leaves
    rw [leaves]
    exact hg
  obtain ⟨label,he⟩ := Q.leavesRetained rootLabel g hgQ
  let f : Signature (OI.K G) 1 := fun x=>g.2 (fun i=>x (Fin.cast hg1 i))
  have literalG : g=(⟨1,f⟩ : AnySignature (OI.K G)) := by
    cases g with
    | mk n table =>
      change n=1 at hg1
      subst n
      rfl
  have literal : (⟨Q.arity label.val,Q.table label⟩ : AnySignature (OI.K G))=⟨1,f⟩ := he.trans literalG
  have retained : (⟨1,f⟩ : AnySignature (OI.K G))∈Q.family := ⟨label,literal⟩
  have single := normalized_leaf (ClosureSourceRows.embedding G) basisB.symm tree
    (root_single G P r) g hg
  change Pn.SingleSupport (normalized G g.2) at single
  rw [literalG] at single
  obtain ⟨bit,c,hc,hf⟩ := Pn.unary_formula _ single
  exact ⟨⟨label,f,literal,retained,currentSignatureAccess G Q ⟨1,f⟩
    (Gadget.realizes_of_mem Q.family .disequality f retained),bit,c,hc,hf⟩⟩

def receipt : Receipt G P r := Classical.choice (exists_receipt G P r)

variable (pin : Receipt G P r)

theorem Receipt.normalized_member : (⟨1,Pn.scaledPin pin.bit pin.coefficient⟩ : AnySignature AlgebraicComplex)∈
    GlobalCloseCompletionBDenseRepresentatives.family G (U.palette G P r) := by
  rw [←pin.exact]
  exact Or.inl ⟨⟨1,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) pin.output⟩,
    ⟨⟨1,pin.output⟩,pin.retained,rfl⟩,rfl⟩

theorem Receipt.both_actual : ∀b,Gadget.Realizes
    (GlobalCloseCompletionBDenseRepresentatives.family G (U.palette G P r)) .disequality
      (Pn.scaledPin b pin.coefficient) :=
  Pn.both_actual _ (GlobalCloseCompletionBCoordinateRealizes.identity _) pin.bit pin.coefficient
    (Gadget.realizes_of_mem _ .disequality _ (pin.normalized_member G P r))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNormalizedPin
end
