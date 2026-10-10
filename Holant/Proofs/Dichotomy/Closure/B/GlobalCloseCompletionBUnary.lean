import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseEscape
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeUnary

/-! The original singular B graph has full support. Its actual saved-factor
saturation supplies a full-support unary in the unchanged source field;
therefore that unary has nonzero native-X self-pairing. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBUnary
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem split_left_full {L : Type} [Field L] {f a b : AnySignature L}
    (s : ProperSplit f a b) (full : ∀x,f.2 x≠0) : ∀x,a.2 x≠0 := by
  intro x zero
  let z := fun i=>Sum.elim x (fun _=>false) (s.ports.symm i)
  apply full z
  rw [s.equation]
  simp only [z,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,zero,mul_zero,zero_mul]

private theorem split_right_full {L : Type} [Field L] {f a b : AnySignature L}
    (s : ProperSplit f a b) (full : ∀x,f.2 x≠0) : ∀x,b.2 x≠0 := by
  intro x zero
  let z := fun i=>Sum.elim (fun _=>false) x (s.ports.symm i)
  apply full z
  rw [s.equation]
  simp only [z,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,zero,mul_zero]

private theorem leaf_full {L : Type} [Field L] {f : AnySignature L} (tree : FactorTree f)
    (full : ∀x,f.2 x≠0) (g : AnySignature L) (member : g∈tree.leaves) : ∀x,g.2 x≠0 := by
  induction tree with
  | leaf f prime =>
    have he : g=f := Multiset.mem_singleton.mp member
    subst g
    exact full
  | split split left right ihl ihr =>
    rcases Multiset.mem_add.mp member with hl|hr
    · exact ihl (split_left_full split full) hl
    · exact ihr (split_right_full split full) hr

private theorem singular_binary_unary_leaf {L : Type} [Field L] (f : Signature L 2)
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

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (r : GlobalCloseCompletionBDenseEscape.SingularReceipt G P)

theorem original_full (b d : Bool) : r.original b d≠0 := by
  obtain ⟨i,j,live,zero⟩ := r.oneHot G P
  have form : r.normalized=(fun b d=>if b=i ∧ d=j then r.normalized i j else 0) := by
    funext b d
    by_cases same : b=i ∧ d=j
    · rcases same with ⟨rfl,rfl⟩
      simp
    · rw [ite_eq_right same]
      exact zero b d (not_and_or.mp same)
  have back := transport_forward basisB.symm (r.original.map (ClosureSourceRows.embedding G))
  change transport basisB.symm (transport basisB (r.original.map (ClosureSourceRows.embedding G)))=_ at back
  rw [r.normalization] at back
  have value : transport basisB.symm (scale r.coefficient r.normalized) b d=
      r.coefficient*r.normalized i j*basisB.matrix b i*basisB.matrix d j := by
    rw [form]
    cases i <;> cases j <;>
      simp [transport,InvertibleKernel.symm,Kernel.mul_apply,Kernel.transpose,scale,mul_comm,mul_left_comm]
  have basis_nonzero (b d : Bool) : basisB.matrix b d≠0 := by
    cases b <;> cases d <;>
      simp [basisB,UB,Signature.equality,Signature.disequality,imaginaryUnit_ne_zero]
  apply (map_ne_zero (ClosureSourceRows.embedding G)).mp
  change r.original.map (ClosureSourceRows.embedding G) b d≠0
  rw [←back,value]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero r.coefficient_nonzero live) (basis_nonzero b i)) (basis_nonzero d j)

def root : AnySignature (OI.K G) := ⟨2,binarySignature r.original⟩
theorem root_nonzero : (root G P r).2≠0 := by
  intro zero
  apply r.nonzero
  funext b d
  exact congrFun zero ![b,d]

def palette : Palette G := ProgrammeSaturation.palette G P (root G P r)
  (root_nonzero G P r) (by change 0<2; decide) r.actual

structure UnaryReceipt : Type 1 where
  label : Fin (palette G P r).count
  output : Signature (OI.K G) 1
  literal : (⟨(palette G P r).arity label.val,(palette G P r).table label⟩ : AnySignature (OI.K G))=⟨1,output⟩
  full : ∀x,output x≠0
  retained : (⟨1,output⟩ : AnySignature (OI.K G))∈(palette G P r).family
  access : CurrentSignatureAccess G (palette G P r) ⟨1,output⟩

theorem unary_exists : Nonempty (UnaryReceipt G P r) := by
  let tree := RetainedFactorCatalogue.tree G (root G P r) (root_nonzero G P r)
  have singular : Matrix.det (binaryMatrix (binarySignature r.original))=0 := r.singular
  obtain ⟨g,hg,hg1⟩ := singular_binary_unary_leaf _ tree singular
  let Q := palette G P r
  let rootLabel := RetainedFactorCatalogue.rootLabel G P (root G P r) (root_nonzero G P r)
  have saved : (⟨⟨Q.arity rootLabel.val,Q.table rootLabel⟩,Q.trees rootLabel⟩ : TreeOccurrence (OI.K G))=
      ⟨root G P r,tree⟩ :=
    ProgrammeSaturation.root_saved G P (root G P r) (root_nonzero G P r) (by change 0<2; decide) r.actual
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
  have rootFull : ∀x : Fin 2→Bool,(root G P r).2 x≠0 := fun x=>original_full G P r (x 0) (x 1)
  have full := leaf_full tree rootFull g hg
  rw [literalG] at full
  exact ⟨⟨label,f,literal,full,retained,currentSignatureAccess G Q ⟨1,f⟩
    (Gadget.realizes_of_mem Q.family .disequality f retained)⟩⟩

def unaryReceipt : UnaryReceipt G P r := Classical.choice (unary_exists G P r)

theorem UnaryReceipt.nonisotropic (u : UnaryReceipt G P r) :
    Signature.connect Signature.disequality (fun b=>u.output (fun _=>b))
      (fun b=>u.output (fun _=>b))≠0 := by
  rw [Signature.connect_disequality]
  have he : u.output (fun _=>false)*u.output (fun _=>true)+
      u.output (fun _=>true)*u.output (fun _=>false)=
      2*(u.output (fun _=>false)*u.output (fun _=>true)) := by ring
  rw [he]
  exact mul_ne_zero (by norm_num) (mul_ne_zero (u.full _) (u.full _))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBUnary
end
