import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeCurrent
import Holant.Proofs.Closure.ProgrammeSaturation
import Holant.Proofs.FiniteGroups.Stabilization.BinaryPrimes
import Holant.Proofs.Hardness.EightVertexGaugePinLeaf
import Holant.Proofs.Hardness.EightVertexGaugePinAccess

/-! A dense-gauge singular receipt exposes a retained scaled computational pin in the
SAME exact output's saturated palette. The generic singular-leaf argument uses
only the established binary-primality and factor-tree facts, together with
the same saturation/access factories; no cyclic endpoint is required.
Singleton support descends through that exact saved tree; the native-X
self-pairing is zero and the original nonzero scalar is retained.
No singular output or unary is called unconditional hardness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeUnary
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinLeaf

/-- A singular binary's exact saved tree contains a unary leaf. This uses
only generic factor-tree arithmetic, independently of any group marking. -/
private theorem singular_binary_unary_leaf {L : Type*} [Field L] (f : Signature L 2)
    (tree : FactorTree (⟨2,f⟩ : AnySignature L))
    (singular : Matrix.det (binaryMatrix f) = 0) :
    ∃ g : AnySignature L, g ∈ tree.leaves ∧ g.1 = 1 := by
  cases tree with
  | leaf f prime =>
    have hp : Prime
        (⟨2,Holant.Projective.BoundedTorsion.binarySignature (binaryMatrix f)⟩ : AnySignature L) := by
      simpa only [binarySignature_binaryMatrix] using prime
    exact False.elim ((prime_binary_nonsingular _ hp) singular)
  | @split f a b split left right =>
    have ha : a.1 = 1 := by
      have h := split.arity
      have hp := split.left_pos
      have hq := split.right_pos
      change a.1+b.1=2 at h
      omega
    cases left with
    | leaf a prime =>
      exact ⟨a,Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self a)),ha⟩
    | split nested l r =>
      have := nested.arity
      have := nested.left_pos
      have := nested.right_pos
      omega

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (r : StableDenseGaugeCurrent.SingularReceipt G P)

def root : AnySignature (OI.K G) := ⟨2,binarySignature r.binary⟩

theorem root_nonzero : (root G P r).2 ≠ 0 := by
  intro zero
  apply r.nonzero
  funext a b
  exact congrFun zero ![a,b]

def palette : Palette G := ProgrammeSaturation.palette G P (root G P r)
  (root_nonzero G P r) (by change 0 < 2; decide) r.actual

abbrev toOriginal := (palette G P r).toOriginal
abbrev fromOriginal := (palette G P r).fromOriginal

theorem old_saved (i : Fin P.count) :
    let Q := palette G P r
    let j := RetainedFactorCatalogue.oldLabel G P (root G P r) (root_nonzero G P r) i
    (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ :=
  ProgrammeSaturation.old_saved G P (root G P r) (root_nonzero G P r)
    (by change 0 < 2; decide) r.actual i

structure UnaryReceipt where
  label : Fin (palette G P r).count
  arity : (palette G P r).arity label.val = 1
  output : Signature (OI.K G) 1
  literal : (⟨(palette G P r).arity label.val,(palette G P r).table label⟩ :
    AnySignature (OI.K G)) = ⟨1,output⟩
  nonzero : output ≠ 0
  pin : ∃ b c, c ≠ 0 ∧ output = fun x => if x 0 = b then c else 0
  retained : (⟨1,output⟩ : AnySignature (OI.K G)) ∈ (palette G P r).family
  access : CurrentSignatureAccess G (palette G P r) ⟨1,output⟩
  accessFactory : access = currentSignatureAccess G (palette G P r) ⟨1,output⟩
    (Gadget.realizes_of_mem (palette G P r).family .disequality output retained)

theorem unary_exists : Nonempty (UnaryReceipt G P r) := by
  let tree := RetainedFactorCatalogue.tree G (root G P r) (root_nonzero G P r)
  have singular : Matrix.det (binaryMatrix (binarySignature r.binary)) = 0 := r.singular
  obtain ⟨g,hg,hg1⟩ := singular_binary_unary_leaf _ tree singular
  let Q := palette G P r
  let rootLabel := RetainedFactorCatalogue.rootLabel G P (root G P r) (root_nonzero G P r)
  have saved : (⟨⟨Q.arity rootLabel.val,Q.table rootLabel⟩,Q.trees rootLabel⟩ :
      TreeOccurrence (OI.K G)) = ⟨root G P r,tree⟩ :=
    ProgrammeSaturation.root_saved G P (root G P r) (root_nonzero G P r)
      (by change 0 < 2; decide) r.actual
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
      change n = 1 at hg1
      subst n
      rfl
  have literal : (⟨Q.arity label.val,Q.table label⟩ : AnySignature (OI.K G)) = ⟨1,f⟩ :=
    he.trans literalG
  have retained : (⟨1,f⟩ : AnySignature (OI.K G)) ∈ Q.family := ⟨label,literal⟩
  have nonzero : f ≠ 0 := by
    have prime := tree.leaves_prime g hg
    rw [literalG] at prime
    exact prime.1
  have rootSingle : SingleSupport (root G P r).2 :=
    binary_support r.binary (StableDenseGaugeCurrent.SingularReceipt.oneHot G P r)
  have single := leaf_support tree rootSingle g hg
  rw [literalG] at single
  have pin := unary_formula f single
  let access := currentSignatureAccess G Q ⟨1,f⟩
    (Gadget.realizes_of_mem Q.family .disequality f retained)
  exact ⟨⟨label,congrArg Sigma.fst literal,f,literal,nonzero,pin,retained,access,rfl⟩⟩

def unaryReceipt : UnaryReceipt G P r := Classical.choice (unary_exists G P r)

/-- Computational pins are isotropic for the mandatory native X pairing. -/
theorem UnaryReceipt.native_isotropic (u : UnaryReceipt G P r) :
    Signature.connect Signature.disequality
      (fun b => u.output (fun _ => b)) (fun b => u.output (fun _ => b)) = 0 := by
  obtain ⟨b,c,_,equal⟩ := u.pin
  rw [equal,Signature.connect_disequality]
  cases b <;> simp

namespace Pin
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinAccess
  (scaledPin both_actual slice slice_actual slice_value dense_slice_nonzero)
end Pin

/-- The opposite bit uses retained I; both pins retain the SAME saved scalar.
This resource receipt makes no assertion about the external-odd terminal. -/
structure PinPairReceipt (u : UnaryReceipt G P r) where
  sourceBit : Bool
  scalar : OI.K G
  nonzero : scalar ≠ 0
  source_literal : u.output = Pin.scaledPin sourceBit scalar
  actual : ∀ b, Gadget.Realizes (palette G P r).family .disequality (Pin.scaledPin b scalar)

theorem UnaryReceipt.pinPair_exists (u : UnaryReceipt G P r) :
    Nonempty (PinPairReceipt G P r u) := by
  obtain ⟨b,c,hc,equal⟩ := u.pin
  have source_literal : u.output = Pin.scaledPin b c := equal
  have original : Gadget.Realizes (palette G P r).family .disequality (Pin.scaledPin b c) := by
    rw [← source_literal]
    exact Gadget.realizes_of_mem (palette G P r).family .disequality _ u.retained
  exact ⟨⟨b,c,hc,source_literal,Pin.both_actual _ ((palette G P r).retainsIdentity G) b c original⟩⟩

def UnaryReceipt.pinPair (u : UnaryReceipt G P r) : PinPairReceipt G P r u :=
  Classical.choice (u.pinPair_exists G P r)

variable {u : UnaryReceipt G P r} (p : PinPairReceipt G P r u)

def PinPairReceipt.pinAccess (b : Bool) :
    CurrentSignatureAccess G (palette G P r) ⟨1,Pin.scaledPin b p.scalar⟩ :=
  currentSignatureAccess G (palette G P r) _ (p.actual b)

def PinPairReceipt.oddSlice (q : Signature (OI.K G) 4) (b : Bool) : Signature (OI.K G) 3 :=
  Pin.slice q (Pin.scaledPin b p.scalar)

theorem PinPairReceipt.oddSlice_literal (q : Signature (OI.K G) 4) (b : Bool)
    (x : Fin 3 → Bool) : p.oddSlice G P r q b x = p.scalar*q ![!b,x 0,x 1,x 2] :=
  Pin.slice_value q b p.scalar x

theorem PinPairReceipt.oddSlice_actual (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q) (b : Bool) :
    Gadget.Realizes (palette G P r).family .disequality (p.oddSlice G P r q b) := by
  have lifted : Gadget.Realizes (palette G P r).family .disequality q := by
    obtain ⟨N,vertices,edges,value⟩ := actual
    exact ⟨N,fun i => ProgrammeSaturation.retains_old G P (root G P r)
      (root_nonzero G P r) (by change 0 < 2; decide) r.actual (vertices i),edges,value⟩
  exact Pin.slice_actual _ ((palette G P r).retainsIdentity G) _ _ lifted (p.actual b)

theorem PinPairReceipt.oddSlice_nonzero (q : Signature (OI.K G) 4)
    (dense : StableDenseParityAlgebra.Dense q) (b : Bool) : p.oddSlice G P r q b ≠ 0 :=
  Pin.dense_slice_nonzero q dense b p.scalar p.nonzero

def PinPairReceipt.oddSliceAccess (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q) (b : Bool) :
    CurrentSignatureAccess G (palette G P r) ⟨3,p.oddSlice G P r q b⟩ :=
  currentSignatureAccess G (palette G P r) _ (p.oddSlice_actual G P r q actual b)

/-- A real retained-unary structural exit on this SAME saved output palette. -/
def UnaryReceipt.exit (u : UnaryReceipt G P r) : StructuralExit G (palette G P r) :=
  .unary u.output u.retained u.nonzero

def structuralExit : StructuralExit G (palette G P r) :=
  (unaryReceipt G P r).exit G P r

theorem family_binary_basis_or_unary {ι : Type}
    (torsion : ResidualTorsion P.family)
    (N : ClosureMarkedDihedral.NativeM
      (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
    (q : ι → Signature (OI.K G) 4) (base : ι)
    (actual : ∀ i, Gadget.Realizes P.family .disequality (q i))
    (even : ∀ i, Holant.LocalDrafts.Hardness.EightVertexNonexception.EvenSupport (q i))
    (dense : ∀ i, StableDenseParityAlgebra.Dense (q i))
    (products : ∀ i, StableDenseResidualAlgebra.Products (q i)) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass
      (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeDenseOutcome.originalFamily
        (fun i => RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (q i)) ∪
       {f | ∃ C : Holant.Marked.Mat, C∈Holant.Marked.groupM N.m ∧ f=⟨2,kernelSignature C⟩}) B) ∨
      ∃ r : StableDenseGaugeCurrent.SingularReceipt G P, Nonempty (UnaryReceipt G P r) := by
  cases StableDenseGaugeCurrent.family_binary_basis_or_original_singular G P torsion N
    q base actual even dense products with
  | inl basis => exact Or.inl basis
  | inr singular =>
    obtain ⟨receipt⟩ := singular
    exact Or.inr ⟨receipt,unary_exists G P receipt⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeUnary
end
