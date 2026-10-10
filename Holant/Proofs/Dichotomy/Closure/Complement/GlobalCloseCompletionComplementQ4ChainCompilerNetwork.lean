import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Templates
import Holant.Complexity.BinaryInterpolation.Chains.Template

/-! Coefficient-independent incidence for positive quaternary chains. Each
join is the literal two-X-edge connection already used by the spectral proof. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork (connect order)
end G
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (Uses Native signature_cast_apply template_denote_heq)
end C
namespace S
export GlobalCloseCompletionComplementQ4Series (ofSpectrum connected_spectrum)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def literal (f : Signature K 4) : ℕ→Network K 4
  | 0=>Network.corolla f
  | k+1=>G.connect (literal f k) (Network.corolla f) false

theorem connect_uses (L R : Network K 4) (F : SignatureFamily K)
    (hL : C.Uses L F) (hR : C.Uses R F) : C.Uses (G.connect L R false) F := by
  intro v
  change (⟨_,(Network.tensorFinite L R).vertex (finSumFinEquiv.symm v)⟩ : AnySignature K)∈F
  cases finSumFinEquiv.symm v with
  | inl v=>exact hL v
  | inr v=>exact hR v

theorem connect_native (L R : Network K 4) (hL : C.Native L) (hR : C.Native R) :
    C.Native (G.connect L R false) := by
  intro e
  refine Fin.cases rfl (fun e=>?_) e
  refine Fin.cases rfl (fun e=>?_) e
  change (Network.tensorFinite L R).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e=>exact hL e
  | inr e=>exact hR e

theorem signature (f : Signature K 4) (k : ℕ) : ∀v,
    (⟨(literal f k).shape.arity v,(literal f k).vertex v⟩ : AnySignature K)=⟨4,f⟩ := by
  have uses : C.Uses (literal f k) {⟨4,f⟩} := by
    induction k with
    | zero=>intro v;rfl
    | succ k ih=>exact connect_uses _ _ _ ih (fun _=>rfl)
  exact uses

theorem arity (f : Signature K 4) (k : ℕ) (v : Fin (literal f k).shape.vertices) :
    (literal f k).shape.arity v=4 := congrArg Sigma.fst (signature f k v)

theorem native (f : Signature K 4) (k : ℕ) : C.Native (literal f k) := by
  induction k with
  | zero=>intro e;exact Fin.elim0 e
  | succ k ih=>exact connect_native _ _ ih (fun e=>Fin.elim0 e)

@[simp] theorem vertices (f : Signature K 4) (k : ℕ) : (literal f k).shape.vertices=k+1 := by
  induction k with
  | zero=>rfl
  | succ k ih=>change (literal f k).shape.vertices+1=k+1+1;rw [ih]

@[simp] theorem edges (f : Signature K 4) (k : ℕ) : (literal f k).shape.edges=2*k := by
  induction k with
  | zero=>rfl
  | succ k ih=>change (literal f k).shape.edges+0+1+1=2*(k+1);rw [ih];omega

theorem connect_shape {J : Type} [Field J] (L R : Network K 4) (L' R' : Network J 4)
    (hL : L.shape=L'.shape) (hR : R.shape=R'.shape) :
    (G.connect L R false).shape=(G.connect L' R' false).shape := by
  rcases L with ⟨SL,vL,eL⟩
  rcases R with ⟨SR,vR,eR⟩
  rcases L' with ⟨SL',vL',eL'⟩
  rcases R' with ⟨SR',vR',eR'⟩
  cases hL
  cases hR
  rfl

theorem shape_independent {J : Type} [Field J] (f : Signature K 4) (g : Signature J 4) (k : ℕ) :
    (literal f k).shape=(literal g k).shape := by
  induction k with
  | zero=>rfl
  | succ k ih=>exact connect_shape _ _ _ _ ih rfl

theorem value [CharZero K] (v : Fin 4→K) (k : ℕ) :
    (literal (S.ofSpectrum v) k).denote=S.ofSpectrum (fun i=>v i^(k+1)) := by
  induction k with
  | zero=>simp [literal,Network.denote_corolla]
  | succ k ih=>
    rw [literal,S.connected_spectrum _ _ _ _ ih (Network.denote_corolla _)]
    congr 1
    funext i
    exact (pow_succ (v i) (k+1)).symm

def shapeTemplate (S : NetworkShape 4) (label edge : ℕ) : Template where
  boundary:=4
  vertices:=List.ofFn fun v : Fin S.vertices=>
    (label,List.ofFn fun i : Fin (S.arity v)=>Labelling.localEndpoint (S.ports ⟨v,i⟩))
  edges:=List.replicate S.edges edge

def labels {s b : ℕ} (a : ℕ→ℕ) (label : Fin s) (hl : a label.val=4) (edge : Fin b)
    (f : Signature K 4) (k : ℕ) : Labelling (literal f k).shape s b a where
  vertex _:=label
  vertex_arity v:=hl.trans (arity f k v).symm
  edge _:=edge

def literalTemplate {s b : ℕ} (a : ℕ→ℕ) (label : Fin s) (hl : a label.val=4) (edge : Fin b)
    (f : Signature K 4) (k : ℕ) : Template := (labels a label hl edge f k).template

theorem template_shape {s b : ℕ} (a : ℕ→ℕ) (label : Fin s) (hl : a label.val=4) (edge : Fin b)
    (f : Signature K 4) (k : ℕ) :
    literalTemplate a label hl edge f k=shapeTemplate (literal f k).shape label.val edge.val := by
  simp [literalTemplate,shapeTemplate,Labelling.template,labels]

def compile (label edge k : ℕ) : Template:=shapeTemplate (literal (K:=ℚ) 0 k).shape label edge

theorem compile_template {s b : ℕ} (a : ℕ→ℕ) (label : Fin s) (hl : a label.val=4) (edge : Fin b)
    (f : Signature K 4) (k : ℕ) : compile label.val edge.val k=literalTemplate a label hl edge f k := by
  rw [template_shape,compile,shape_independent (0 : Signature ℚ 4) f k]

theorem valid {s b : ℕ} (a : ℕ→ℕ) (label : Fin s) (hl : a label.val=4) (edge : Fin b) (k : ℕ) :
    (compile label.val edge.val k).WellFormed s b a := by
  rw [compile_template a label hl edge (0 : Signature ℚ 4) k]
  exact (labels a label hl edge (0 : Signature ℚ 4) k).wellFormed

@[simp] theorem compile_boundary (label edge k : ℕ) : (compile label edge k).boundary=4 := rfl
@[simp] theorem compile_vertices (label edge k : ℕ) : (compile label edge k).vertices.length=k+1 := by
  simp [compile,shapeTemplate]
@[simp] theorem compile_edges (label edge k : ℕ) : (compile label edge k).edges.length=2*k := by
  simp [compile,shapeTemplate]

theorem template_value [CharZero K] {s b : ℕ} (a : ℕ→ℕ)
    (label : Fin s) (hl : a label.val=4) (edge : Fin b) (v : Fin 4→K) (k : ℕ)
    (H : (i : Fin s)→Signature K (a i.val)) (E : Fin b→Kernel K)
    (hf : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,S.ofSpectrum v⟩)
    (hx : E edge=Signature.disequality) :
    ((compile label.val edge.val k).network (valid a label hl edge k) H E).denote=
      S.ofSpectrum (fun i=>v i^(k+1)) := by
  have same:=C.template_denote_heq _ _ (valid a label hl edge k)
    (labels a label hl edge (S.ofSpectrum v) k).wellFormed
    (compile_template a label hl edge (S.ofSpectrum v) k) H E
  refine (eq_of_heq same).trans ((?_ :
    ((literalTemplate a label hl edge (S.ofSpectrum v) k).network
      (labels a label hl edge (S.ofSpectrum v) k).wellFormed H E).denote=
        (literal (S.ofSpectrum v) k).denote).trans (value v k))
  apply Labelling.denote_template_of_labels
  · intro u x
    change H label (fun i=>x (Fin.cast (hl.trans (arity (S.ofSpectrum v) k u).symm) i))=
      (literal (S.ofSpectrum v) k).vertex u x
    apply C.signature_cast_apply
    exact hf.trans (signature (S.ofSpectrum v) k u).symm
  · intro e p q
    exact congrFun₂ (hx.trans (native (S.ofSpectrum v) k e).symm) p q


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerNetwork
end
