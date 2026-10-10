import Holant.Proofs.Closure.ClosureCyclicCurrentEndpoint
import Holant.Proofs.Closure.ClosureCyclicCurrentBinaryPrime

/-! A singular actual outside binary exposes a nonzero unary in its SAME saved
saturated tree. The returned label/tree and both physical original-G programmes
are actual palette data; no prime-binary premise is imposed on OutsideCard. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain

theorem singular_binary_unary_leaf {L : Type*} [Field L] (f : Signature L 2)
    (tree : FactorTree (⟨2,f⟩ : AnySignature L)) (singular : Matrix.det (binaryMatrix f) = 0) :
    ∃ g : AnySignature L, g ∈ tree.leaves ∧ g.1 = 1 := by
  cases tree with
  | leaf f prime =>
    have hp : Prime (⟨2,Holant.Projective.BoundedTorsion.binarySignature (binaryMatrix f)⟩ : AnySignature L) := by
      simpa only [binarySignature_binaryMatrix] using prime
    exact False.elim ((prime_binary_nonsingular _ hp) singular)
  | @split f a b split left right =>
    have ha : a.1 = 1 := by have h := split.arity; have hp := split.left_pos; have hq := split.right_pos; change a.1+b.1=2 at h; omega
    cases left with
    | leaf a prime =>
      exact ⟨a,Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self a)),ha⟩
    | split nested l r =>
      have := nested.arity
      have := nested.left_pos
      have := nested.right_pos
      omega

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) {m : ℕ} (o : OutsideReceipt G P m)

/-- Literal unary root label in the actual outside output's saturated palette. -/
structure UnaryReceipt where
  label : Fin (OutsideReceipt.palette G P o).count
  arity : (OutsideReceipt.palette G P o).arity label.val = 1
  output : Signature (OI.K G) 1
  literal : (⟨(OutsideReceipt.palette G P o).arity label.val,
      (OutsideReceipt.palette G P o).table label⟩ : AnySignature (OI.K G)) = ⟨1,output⟩
  nonzero : output ≠ 0
  retained : (⟨1,output⟩ : AnySignature (OI.K G)) ∈ (OutsideReceipt.palette G P o).family
  access : CurrentSignatureAccess G (OutsideReceipt.palette G P o) ⟨1,output⟩
  accessFactory : access = currentSignatureAccess G (OutsideReceipt.palette G P o) ⟨1,output⟩
    (Gadget.realizes_of_mem (OutsideReceipt.palette G P o).family .disequality output retained)

include o in
theorem unaryReceipt_exists (singular : Matrix.det (binaryMatrix (OutsideReceipt.output G P o)) = 0) :
    Nonempty (UnaryReceipt G P o) := by
  let root : AnySignature (OI.K G) := ⟨2,OutsideReceipt.output G P o⟩
  let hn : root.2 ≠ 0 := ProjectiveOutput.source_nonzero G P o.card.signature o.access o.card.nonzero
  let tree := RetainedFactorCatalogue.tree G root hn
  obtain ⟨g,hg,hg1⟩ := singular_binary_unary_leaf _ tree singular
  let Q := OutsideReceipt.palette G P o
  let rootLabel := RetainedFactorCatalogue.rootLabel G P root hn
  have saved : (⟨⟨Q.arity rootLabel.val,Q.table rootLabel⟩,Q.trees rootLabel⟩ : TreeOccurrence (OI.K G)) =
      ⟨root,tree⟩ := ProjectiveOutput.root_saved G P o.card.signature o.access (by norm_num) o.card.nonzero
  have leaves := congrArg (fun z : TreeOccurrence (OI.K G) => z.2.leaves) saved
  have hgQ : g ∈ (Q.trees rootLabel).leaves := by
    change (Q.trees rootLabel).leaves = tree.leaves at leaves
    rw [leaves]
    exact hg
  obtain ⟨label,he⟩ := Q.leavesRetained rootLabel g hgQ
  let f : Signature (OI.K G) 1 := fun x => g.2 (fun i => x (Fin.cast hg1 i))
  have literalG : g = (⟨1,f⟩ : AnySignature (OI.K G)) := by
    cases g with
    | mk n table =>
      change n=1 at hg1
      subst n
      rfl
  have literal : (⟨Q.arity label.val,Q.table label⟩ : AnySignature (OI.K G)) = ⟨1,f⟩ := he.trans literalG
  have retained : (⟨1,f⟩ : AnySignature (OI.K G)) ∈ Q.family := ⟨label,literal⟩
  have nonzero : f ≠ 0 := by
    have prime := tree.leaves_prime g hg
    rw [literalG] at prime
    exact prime.1
  let access := currentSignatureAccess G Q ⟨1,f⟩ (Gadget.realizes_of_mem Q.family .disequality f retained)
  exact ⟨⟨label,(congrArg Sigma.fst literal),f,literal,nonzero,retained,access,rfl⟩⟩

def unaryReceipt (singular : Matrix.det (binaryMatrix (OutsideReceipt.output G P o)) = 0) : UnaryReceipt G P o :=
  Classical.choice (unaryReceipt_exists G P o singular)

/-- Genuine retained unary structural exit at the SAME actual saturated palette. -/
def UnaryReceipt.exit (u : UnaryReceipt G P o) : StructuralExit G (OutsideReceipt.palette G P o) :=
  .unary u.output u.retained u.nonzero

/-- The nonsingular alternative keeps its real outside binary label; singular
outputs expose the actual nonzero unary leaf instead of a fake prime binary. -/
inductive OutsideDomain : Type 1
  | unary (receipt : UnaryReceipt G P o)
  | binary (nonsingular : Matrix.det (binaryMatrix (OutsideReceipt.output G P o)) ≠ 0)

def outsideDomain : OutsideDomain G P o := by
  classical
  by_cases singular : Matrix.det (binaryMatrix (OutsideReceipt.output G P o)) = 0
  · exact .unary (unaryReceipt G P o singular)
  · exact .binary singular
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
