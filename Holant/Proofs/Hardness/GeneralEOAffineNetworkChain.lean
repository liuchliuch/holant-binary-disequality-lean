import Holant.Proofs.Hardness.GeneralEOAffinePlaneDEQ
import Holant.Proofs.Hardness.GeneralEOAffinePlaneChainOccurrences

/-! The affine-plane supplier can be an arbitrary actual four-port network.
Every copy retains all its original vertex labels and internal native edges.
The 24-copy macro adds precisely 46 crossed native-X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkChain
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOAffinePlaneChain (copies table Mat binary)
end C
namespace L
export GeneralEOAffinePlaneChainLabels (copies copies_exact kernels)
end L
namespace B
export BinaryInterpolation.Chains (reindex reindex_denote Native)
end B
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (N : Network K 4) (NL : Labelling N.shape s 1 a)
variable (e : Equiv.Perm (Fin 4))

def network (k : ℕ) : Network K 4 := C.copies (B.reindex N e) k

def labels (k : ℕ) : Labelling (network N e k).shape s 1 a :=
  L.copies (B.reindex N e) (LabelledNetwork.reindex N NL e) k

@[simp] theorem vertices (k : ℕ) :
    (network N e k).shape.vertices=(k+1)*N.shape.vertices := by
  exact GeneralEOAffinePlaneChain.copies_vertices (B.reindex N e) k

@[simp] theorem edges (k : ℕ) :
    (network N e k).shape.edges=(k+1)*N.shape.edges+2*k := by
  exact GeneralEOAffinePlaneChain.copies_edges (B.reindex N e) k

theorem exact (G : (i : Fin s)→Signature K (a i.val))
    (hN : LabelledNetwork.Exact G N NL) (k : ℕ) :
    LabelledNetwork.Exact G (network N e k) (labels N NL e k) :=
  L.copies_exact G _ _ (LabelledNetwork.exact_reindex N NL G hN e) k

theorem native (hn : ∀i,N.edge i=Signature.disequality) (k : ℕ) :
    B.Native (network N e k) :=
  GeneralEOAffinePlaneChain.copies_native (B.reindex N e) hn k

private theorem apply_eq {n m : ℕ} (f : Signature K n) (g : Signature K m)
    (h : (⟨n,f⟩ : AnySignature K)=⟨m,g⟩) (hn : n=m) (x : Fin m→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by
  subst m
  have hf : f=g := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  simpa only [Fin.cast_eq_self] using congrFun hf x

theorem template_actual (G : (i : Fin s)→Signature K (a i.val))
    (hN : LabelledNetwork.Exact G N NL)
    (hn : ∀i,N.edge i=Signature.disequality) (k : ℕ) :
    ((labels N NL e k).template.network (labels N NL e k).wellFormed G L.kernels).denote=
      (network N e k).denote := by
  apply Labelling.denote_template_of_labels (labels N NL e k) G L.kernels
    (network N e k).vertex (network N e k).edge
  · intro v x
    exact apply_eq _ _ (exact N NL e G hN k v) ((labels N NL e k).vertex_arity v) x
  · intro i x y
    exact congrFun₂ (native N e hn k i).symm x y

theorem power_denote (f : Signature K 2)
    (hplane : Tensor.reindex e N.denote=EOBinaryPlaneCore.lift f)
    (k : ℕ) (c : K) (hp : C.table f^(k+1)=c • (1 : C.Mat (K:=K))) :
    (network N e k).denote=c • ExactTwoSignatures.E := by
  have hn : (B.reindex N e).denote=EOBinaryPlaneCore.lift (C.binary (C.table f)) := by
    rw [B.reindex_denote,GeneralEOAffinePlaneChain.binary_table]
    exact hplane
  rw [network,GeneralEOAffinePlaneChain.copies_denote _ _ hn k,hp,
    GeneralEOAffinePlaneDEQ.lifted_scalar]

@[simp] theorem template_vertices (k : ℕ) :
    (labels N NL e k).template.vertices.length=(k+1)*N.shape.vertices := by
  rw [Labelling.vertices_length,vertices]

@[simp] theorem template_edges (k : ℕ) :
    (labels N NL e k).template.edges.length=(k+1)*N.shape.edges+2*k := by
  rw [Labelling.edges_length,edges]

/-- Multiplicity of every original label, including coincident signatures. -/
theorem copies_count (N : Network K 4) (NL : Labelling N.shape s 1 a)
    (j : Fin s) (k : ℕ) :
    LabelledNetwork.count (L.copies N NL k) j=(k+1)*LabelledNetwork.count NL j := by
  induction k with
  | zero => simp [L.copies]
  | succ k ih =>
    change LabelledNetwork.count
      (LabelledNetwork.tensor (C.copies N k) N (L.copies N NL k) NL) j=_
    rw [LabelledNetwork.count_tensor,ih]
    simp only [Nat.add_mul,Nat.one_mul]

theorem label_occurrences (j : Fin s) (k : ℕ) :
    ((labels N NL e k).template.vertices.filter (fun row=>row.1=j.val)).length=
      (k+1)*LabelledNetwork.count NL j := by
  rw [LabelledNetwork.template_count]
  exact copies_count (B.reindex N e) (LabelledNetwork.reindex N NL e) j k

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkChain
