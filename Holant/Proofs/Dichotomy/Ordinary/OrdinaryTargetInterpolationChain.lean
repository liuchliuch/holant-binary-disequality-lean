import Holant.Complexity.BinaryInterpolation.Chains.RecordCorrespondence

/-! The existing executable positive-chain records, interpreted with ordinary
identity edges. Incidence, labels, port order and chain length are unchanged.
The exact matrix is B^(k+1), rather than the native-X transfer power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationChain
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.Complexity.BinaryInterpolation.Chains
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n : ℕ}

def ordinary (N : Network K n) : Network K n where
  shape := N.shape
  vertex := N.vertex
  edge _ := Signature.equality

def seriesI (L R : Network K 2) : Network K 2 :=
  (reindex (tensor L R) seriesOrder).contract Signature.equality

theorem ordinary_series (L R : Network K 2) :
    (ordinary (series L R)).denote=(seriesI (ordinary L) (ordinary R)).denote := by
  apply Network.denote_congr
  · intro v x
    change (Network.tensorFinite L R).vertex (finSumFinEquiv.symm v) x=
      (Network.tensorFinite (ordinary L) (ordinary R)).vertex (finSumFinEquiv.symm v) x
    have vertices : (Network.tensorFinite L R).vertex=
        (Network.tensorFinite (ordinary L) (ordinary R)).vertex := by
      funext q
      cases q <;> rfl
    exact congrFun (congrFun vertices (finSumFinEquiv.symm v)) x
  · intro e a b
    refine Fin.cases rfl (fun e=>?_) e
    change Signature.equality a b=(Network.tensorFinite (ordinary L) (ordinary R)).edge
      (finSumFinEquiv.symm e) a b
    cases finSumFinEquiv.symm e <;> rfl

theorem seriesI_denote (L R : Network K 2) (A B : Binary (K:=K))
    (hL : L.denote=binarySignature A) (hR : R.denote=binarySignature B) :
    (seriesI L R).denote=binarySignature (A*B) := by
  rw [seriesI,Network.denote_contract,reindex_denote,tensor_denote,hL,hR]
  funext x
  change (∑a : Bool,∑b : Bool,Signature.equality a b*(A (x 0) a*B b (x 1)))=
    ∑b : Bool,A (x 0) b*B b (x 1)
  simp [Signature.equality]

theorem ordinary_corolla (B : Binary (K:=K)) :
    (ordinary (Network.corolla (binarySignature B))).denote=binarySignature B := by
  calc
    _ = (Network.corolla (binarySignature B)).denote := by
      apply Network.denote_congr
      · intro v x
        rfl
      · intro e
        exact Fin.elim0 e
    _ = _ := Network.denote_corolla _

theorem ordinary_literal_denote (B : Binary (K:=K)) (k : ℕ) :
    (ordinary (literal B k)).denote=binarySignature (B^(k+1)) := by
  induction k with
  | zero=>simpa only [literal,copies,Nat.zero_add,pow_one] using ordinary_corolla B
  | succ k ih=>
    change (ordinary (series (literal B k) (Network.corolla (binarySignature B)))).denote=_
    rw [ordinary_series,seriesI_denote _ _ _ _ ih (ordinary_corolla B)]
    simp only [pow_succ]

theorem literalTemplate_denote_I {s b : ℕ} (arity : ℕ→ℕ)
    (label : Fin s) (hlabel : arity label.val=2) (edge : Fin b)
    (B : Binary (K:=K)) (k : ℕ)
    (signatures : (i : Fin s)→Signature K (arity i.val))
    (kernels : Fin b→Bool→Bool→K)
    (hB : (⟨arity label.val,signatures label⟩ : AnySignature K)=⟨2,binarySignature B⟩)
    (hI : kernels edge=Signature.equality) :
    ((literalTemplate arity label hlabel edge B k).network
      (literalTemplate_wellFormed arity label hlabel edge B k) signatures kernels).denote=
      binarySignature (B^(k+1)) := by
  rw [←ordinary_literal_denote B k]
  apply Labelling.denote_template_of_labels
  · intro v x
    change signatures label (fun i=>x (Fin.cast
      (hlabel.trans (literal_arity B k v).symm) i))=(literal B k).vertex v x
    apply signature_cast_apply
    exact hB.trans (literal_signature B k v).symm
  · intro e a b
    exact congrFun₂ hI a b

theorem compile_denote_I {s b : ℕ} (arity : ℕ→ℕ)
    (label : Fin s) (hlabel : arity label.val=2) (edge : Fin b) (k : ℕ)
    (B : Binary (K:=K))
    (signatures : (i : Fin s)→Signature K (arity i.val))
    (kernels : Fin b→Bool→Bool→K)
    (hB : (⟨arity label.val,signatures label⟩ : AnySignature K)=⟨2,binarySignature B⟩)
    (hI : kernels edge=Signature.equality) :
    ((compile label.val edge.val k).network
      (compile_wellFormed arity label hlabel edge k) signatures kernels).denote=
      binarySignature (B^(k+1)) := by
  have he := template_denote_heq _ _ (compile_wellFormed arity label hlabel edge k)
    (literalTemplate_wellFormed arity label hlabel edge B k)
    (compile_eq_literalTemplate arity label hlabel edge B k) signatures kernels
  exact (eq_of_heq he).trans
    (literalTemplate_denote_I arity label hlabel edge B k signatures kernels hB hI)

/-- The actual compiler records used by the interpolation query have the
ordinary matrix-power semantics, for arbitrary (not only diagonal) B. -/
theorem explicitTemplate_denote_I {s b : ℕ} (arity : ℕ→ℕ)
    (label : Fin s) (hlabel : arity label.val=2) (edge : Fin b) (k : ℕ)
    (B : Binary (K:=K))
    (signatures : (i : Fin s)→Signature K (arity i.val))
    (kernels : Fin b→Bool→Bool→K)
    (hB : (⟨arity label.val,signatures label⟩ : AnySignature K)=⟨2,binarySignature B⟩)
    (hI : kernels edge=Signature.equality) :
    ((explicitTemplate label.val edge.val k).network
      (explicitTemplate_wellFormed arity label hlabel edge k) signatures kernels).denote=
      binarySignature (B^(k+1)) := by
  have he := template_denote_heq _ _ (explicitTemplate_wellFormed arity label hlabel edge k)
    (compile_wellFormed arity label hlabel edge k)
    (compile_eq_explicitTemplate label.val edge.val k).symm signatures kernels
  exact (eq_of_heq he).trans (compile_denote_I arity label hlabel edge k B signatures kernels hB hI)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationChain
end
