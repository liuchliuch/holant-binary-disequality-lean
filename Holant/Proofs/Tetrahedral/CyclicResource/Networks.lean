import Holant.Proofs.Algorithms.CyclicBoundary.AlgebraicSource
import Holant.Proofs.Algorithms.CyclicBoundary.DoubledDescent


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Certificates.FourthRootOdd
open Holant.LocalDrafts.MainChain.CyclicBoundary
noncomputable section
set_option backward.isDefEq.respectTransparency false

def copies {n : ℕ} (M : Network ℂ n) : ℕ :=
  ∑ v : Fin M.shape.vertices, if M.shape.arity v = 4 then 1 else 0

/-- A vertex is charged by its designated resource type, not by testing
equality of tensor values. All auxiliary leaves below have arity two. -/
inductive Circuit {ι : Type*} (q : Signature ℂ 4) (B : ι → Kernel ℂ) : ℕ → Type _
  | input : Circuit q B 4
  | auxiliary (i : ι) : Circuit q B 2
  | reorder {n} (C : Circuit q B n) (p : Equiv.Perm (Fin n)) : Circuit q B n
  | tensor {m n} (L : Circuit q B m) (R : Circuit q B n) : Circuit q B (m+n)
  | contract {n} (C : Circuit q B (n+2)) : Circuit q B n

variable {ι : Type*} {q : Signature ℂ 4} {B : ι → Kernel ℂ}

def Circuit.network : {n : ℕ} → Circuit q B n → Network ℂ n
  | _, .input => singleVertexNetwork q
  | _, .auxiliary i => singleVertexNetwork (PhysicalAttachments.binary (B i))
  | _, .reorder C p => reorderNetwork C.network p
  | _, .tensor L R => L.network.tensor R.network
  | _, .contract C => C.network.contract Signature.disequality

def Circuit.calls : {n : ℕ} → Circuit q B n → ℕ
  | _, .input => 1
  | _, .auxiliary _ => 0
  | _, .reorder C _ => C.calls
  | _, .tensor L R => L.calls + R.calls
  | _, .contract C => C.calls

theorem copies_tensor {m n : ℕ} (L : Network ℂ m) (R : Network ℂ n) :
    copies (L.tensor R) = copies L + copies R := by
  classical
  let f : Fin L.shape.vertices ⊕ Fin R.shape.vertices → ℕ :=
    fun v => if Sum.elim L.shape.arity R.shape.arity v = 4 then 1 else 0
  change (∑ v, f ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)) = _
  rw [(Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm.sum_comp]
  rw [Fintype.sum_sum_type]
  rfl

/-- Literal graph count, derived from the construction rather than supplied. -/
theorem Circuit.count {n} (C : Circuit q B n) : copies C.network = C.calls := by
  induction C with
  | input => simp [network,calls,copies,singleVertexNetwork]
  | auxiliary i => simp [network,calls,copies,singleVertexNetwork]
  | reorder C p ih => exact ih
  | tensor L R ihL ihR => simpa only [network,calls,copies_tensor,ihL,ihR]
  | contract C ih => exact ih

def retained (q : Signature ℂ 4) (B : ι → Kernel ℂ) : SignatureFamily ℂ :=
  {s | s = ⟨4,q⟩ ∨ ∃ i, s = ⟨2,PhysicalAttachments.binary (B i)⟩}

theorem Circuit.labels {n} (C : Circuit q B n) :
    ∀ v, (⟨C.network.shape.arity v,C.network.vertex v⟩ : AnySignature ℂ) ∈ retained q B := by
  induction C with
  | input => intro v; exact Or.inl rfl
  | auxiliary i => intro v; exact Or.inr ⟨i,rfl⟩
  | reorder C p ih => exact ih
  | contract C ih => exact ih
  | tensor L R ihL ihR =>
    intro v
    change (⟨_,(Network.tensorFinite L.network R.network).vertex
      ((Fintype.equivFin (Fin L.network.shape.vertices ⊕ Fin R.network.shape.vertices)).symm v)⟩
      : AnySignature ℂ) ∈ retained q B
    cases (Fintype.equivFin (Fin L.network.shape.vertices ⊕ Fin R.network.shape.vertices)).symm v with
    | inl v => exact ihL v
    | inr v => exact ihR v

theorem Circuit.native {n} (C : Circuit q B n) :
    ∀ e, C.network.edge e = Signature.disequality := by
  induction C with
  | input => intro e; exact Fin.elim0 e
  | auxiliary i => intro e; exact Fin.elim0 e
  | reorder C p ih => exact ih
  | contract C ih => intro e; exact Fin.cases rfl ih e
  | tensor L R ihL ihR =>
    intro e
    change (Network.tensorFinite L.network R.network).edge
      ((Fintype.equivFin (Fin L.network.shape.edges ⊕ Fin R.network.shape.edges)).symm e) = _
    cases (Fintype.equivFin (Fin L.network.shape.edges ⊕ Fin R.network.shape.edges)).symm e with
    | inl e => exact ihL e
    | inr e => exact ihR e

theorem Circuit.actual {n} (C : Circuit q B n) :
    Gadget.Realizes (retained q B) .disequality C.network.denote :=
  Gadget.realizes_network C.network (retained q B) .disequality C.labels C.native

/-- Realization over the original family is separate from the retained-label
count: projective substitution can expand auxiliary labels into many vertices. -/
theorem Circuit.substitute {n} (C : Circuit q B n) (F : SignatureFamily ℂ)
    (hq : Gadget.RealizesUpTo F .disequality q)
    (hB : ∀ i, Gadget.Realizes F .disequality (PhysicalAttachments.binary (B i))) :
    Gadget.RealizesUpTo F .disequality C.network.denote := by
  apply Holant.OpenNetworkComposition.realizesUpTo_network
  · intro v
    rcases C.labels v with he | ⟨i,he⟩
    · exact Eq.mp (congrArg (fun t : AnySignature ℂ => Gadget.RealizesUpTo F .disequality t.2) he.symm) hq
    · have hr : Gadget.RealizesUpTo F .disequality (PhysicalAttachments.binary (B i)) := by
        refine ⟨1,one_ne_zero,?_⟩
        simpa only [one_mul] using hB i
      exact Eq.mp (congrArg (fun t : AnySignature ℂ => Gadget.RealizesUpTo F .disequality t.2) he.symm) hr
  · exact C.native
  · norm_num

/-- Exact scalar/port result of a concrete counted template. k is an index
derived by constructors, not an extra bound on an unrelated realization. -/
structure Certificate (q : Signature ℂ 4) (B : ι → Kernel ℂ)
    {n : ℕ} (f : Signature ℂ n) (k : ℕ) where
  circuit : Circuit q B n
  calls_eq : circuit.calls = k
  scalar : ℂ
  scalar_ne_zero : scalar ≠ 0
  equation : circuit.network.denote = scalar • f

theorem Certificate.count {n k} {f : Signature ℂ n} (W : Certificate q B f k) :
    copies W.circuit.network = k := W.circuit.count.trans W.calls_eq

def input (q : Signature ℂ 4) (B : ι → Kernel ℂ) : Certificate q B q 1 :=
  ⟨.input,rfl,1,one_ne_zero,by simpa only [Circuit.network, one_smul] using singleVertexNetwork_denote q⟩

def Certificate.rescale {n k} {f : Signature ℂ n} {c : ℂ}
    (W : Certificate q B (c • f) k) (hc : c ≠ 0) : Certificate q B f k :=
  ⟨W.circuit,W.calls_eq,W.scalar*c,mul_ne_zero W.scalar_ne_zero hc,
    by rw [W.equation,smul_smul]⟩

def Certificate.reorder {n k} {f : Signature ℂ n} (W : Certificate q B f k)
    (p : Equiv.Perm (Fin n)) : Certificate q B (Tensor.reindex p f) k := by
  refine ⟨.reorder W.circuit p,W.calls_eq,W.scalar,W.scalar_ne_zero,?_⟩
  rw [Circuit.network,reorderNetwork_denote,W.equation]
  rfl

theorem Certificate.actual_original {n k} {f : Signature ℂ n} (W : Certificate q B f k)
    (F : SignatureFamily ℂ) (hq : Gadget.RealizesUpTo F .disequality q)
    (hB : ∀ i, Gadget.Realizes F .disequality (PhysicalAttachments.binary (B i))) :
    Gadget.RealizesUpTo F .disequality f := by
  obtain ⟨c,hc,hr⟩ := W.circuit.substitute F hq hB
  refine ⟨c*W.scalar,mul_ne_zero hc W.scalar_ne_zero,?_⟩
  rw [W.equation] at hr
  simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using hr

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
