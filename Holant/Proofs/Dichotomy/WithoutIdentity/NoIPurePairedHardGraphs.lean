import Holant.NetworkAlgebra
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePairedHardForm

/-! Exact ambient mapping and finite serialization of actual native graphs.
The macro family preserves every selected row and its original arity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHardGraphs
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K:=K.algebra'
variable {s : ℕ} {a : ℕ→ℕ} (H : (i : Fin s)→Signature K (a i.val))

def ambient (i : Fin s) : Signature AlgebraicComplex (a i.val):=fun z=>(H i z : AlgebraicComplex)

def mapped {n : ℕ} (N : NativeAntiTargetSource.Output H n) :
    NativeAntiTargetSource.Output (ambient K H) n where
  network:=N.network.map K.subtype
  labels:=N.labels
  exact:=fun v=>congrArg (fun f : AnySignature K=>(⟨f.1,fun z=>(f.2 z : AlgebraicComplex)⟩ : AnySignature AlgebraicComplex)) (N.exact v)
  native:=by
    intro e
    funext x y
    change (N.network.edge e x y : AlgebraicComplex)=Signature.disequality x y
    rw [N.native]
    cases x <;> cases y <;> rfl

@[simp] theorem mapped_denote {n : ℕ} (N : NativeAntiTargetSource.Output H n) :
    (mapped K H N).network.denote=fun z=>(N.network.denote z : AlgebraicComplex) := by
  funext z
  exact Network.denote_map K.subtype N.network z

variable {t : ℕ} (row : Fin t→AnySignature AlgebraicComplex)
variable (N : (i : Fin t)→NativeAntiTargetSource.Output H (row i).1)
variable (form : ∀i,(fun z=>((N i).network.denote z : AlgebraicComplex))=(row i).2)

def templates (k : ℕ) : Template:=
  if h:k<t then (N ⟨k,h⟩).template else ⟨0,[],[]⟩

theorem templates_at (i : Fin t) : templates K H row N i.val=(N i).template := by
  simp only [templates,dite_eq_left i.isLt]

theorem valid : ∀k<t,(templates K H row N k).WellFormed s 1 a := by
  intro k hk
  rw [templates_at K H row N ⟨k,hk⟩]
  exact (N ⟨k,hk⟩).labels.wellFormed

def table (i : Fin t) : Signature AlgebraicComplex
    ((templates K H row N i.val).boundary):=
  ((templates K H row N i.val).network (valid K H row N i.val i.isLt)
    (ambient K H) (fun _ : Fin 1=>Signature.disequality)).denote

def signature (i : Fin t) : AnySignature AlgebraicComplex:=
  ⟨(templates K H row N i.val).boundary,table K H row N i⟩

private theorem template_any_congr (T U : Template) (h : T=U)
    (ht : T.WellFormed s 1 a) (hu : U.WellFormed s 1 a) :
    (⟨T.boundary,(T.network ht (ambient K H)
      (fun _ : Fin 1=>Signature.disequality)).denote⟩ : AnySignature AlgebraicComplex)=
    ⟨U.boundary,(U.network hu (ambient K H)
      (fun _ : Fin 1=>Signature.disequality)).denote⟩ := by
  cases h
  rfl

include form in
theorem signature_exact (i : Fin t) : signature K H row N i=row i := by
  have ht:=template_any_congr K H (templates K H row N i.val) (N i).template
    (templates_at K H row N i) (valid K H row N i.val i.isLt) (N i).labels.wellFormed
  have hn:=NativeAntiTargetSource.template_exact (ambient K H)
    (mapped K H (N i))
  rw [mapped_denote,form i] at hn
  exact ht.trans (congrArg (fun f=>(⟨(row i).1,f⟩ : AnySignature AlgebraicComplex)) hn)

include form in
theorem family_exact : Set.range (signature K H row N)=Set.range row := by
  apply Set.ext
  intro f
  change (∃i,signature K H row N i=f)↔∃i,row i=f
  simp only [signature_exact K H row N form]

section Pair
variable {m n : ℕ} (h : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
variable (Nh : NativeAntiTargetSource.Output H (m*2))
variable (Ng : NativeAntiTargetSource.Output H (n*2))

def pairRow : Fin 2→AnySignature AlgebraicComplex:=![⟨m*2,NoIPurePairedHardForm.paired h⟩,⟨n*2,NoIPurePairedHardForm.paired g⟩]

def pairGraph (i : Fin 2) : NativeAntiTargetSource.Output H (pairRow h g i).1 :=
  Fin.cases Nh (fun j=>Fin.cases Ng (fun k=>Fin.elim0 k) j) i

theorem pair_range : Set.range (pairRow h g)={⟨m*2,NoIPurePairedHardForm.paired h⟩,⟨n*2,NoIPurePairedHardForm.paired g⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [pairRow]
  · intro hf
    rcases Set.mem_insert_iff.mp hf with rfl|hf
    · exact ⟨0,rfl⟩
    · exact ⟨1,(Set.mem_singleton_iff.mp hf).symm⟩

end Pair


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHardGraphs
end
