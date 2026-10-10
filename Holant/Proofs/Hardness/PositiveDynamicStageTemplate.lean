import Holant.Proofs.Hardness.PositiveDynamicStage

/-! Original-q/native-X literal templates for fully inlined positive dynamic
stages. The compiler is incidence-only and never introduces a staged palette
label. This file proves semantic correctness and exact occurrence counts. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStageTemplate
open Holant Holant.Complexity FixedGadgetSubstitution
namespace D
export PositiveDynamicStage
  (A B C stage blockChain blockChain_denote blockChain_counts blockChain_signature
   blockChain_arity blockChain_native)
end D
namespace T
export ExactTwoChainTemplate (shapeTemplate series_shape_independent)
end T
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains
  (reindex signature_cast_apply template_denote_heq)
end Chain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

theorem reindex_shape_independent {J : Type*} [Field J] {n : ℕ}
    (N : Network K n) (M : Network J n) (h : N.shape=M.shape) (p : Equiv.Perm (Fin n)) :
    (Chain.reindex N p).shape=(Chain.reindex M p).shape := by
  cases N with | mk S v e =>
    cases M with | mk S' v' e' =>
      cases h
      rfl

theorem stage_shape_same (a b c : K) (n : ℕ) :
    (D.stage a b c n).shape=(D.stage (K:=ℚ) 0 0 0 n).shape := by
  apply reindex_shape_independent
  exact (ThreeModeChain.shape_same a b c (n-1)).trans
    (ThreeModeChain.shape_same (0 : ℚ) 0 0 (n-1)).symm

theorem blockChain_shape_same (a b c : K) (n k : ℕ) :
    (D.blockChain a b c n k).shape=(D.blockChain (K:=ℚ) 0 0 0 n k).shape := by
  induction k with
  | zero => exact stage_shape_same a b c n
  | succ k ih => exact T.series_shape_independent _ _ _ _ ih (stage_shape_same a b c n)

/-- Rational zeros select an incidence shape only; every emitted vertex label
is the supplied original-q label. -/
def compile (label edge n k : ℕ) : Template :=
  T.shapeTemplate (D.blockChain (K:=ℚ) 0 0 0 n k).shape label edge

@[simp] theorem boundary (label edge n k : ℕ) : (compile label edge n k).boundary=4 := rfl

theorem counts (label edge n k : ℕ) (hn : 0<n) :
    (compile label edge n k).vertices.length=n*(k+1) ∧
      (compile label edge n k).edges.length=2*n*(k+1)-2 := by
  simpa only [compile,T.shapeTemplate,List.length_ofFn,List.length_replicate] using
    D.blockChain_counts (0 : ℚ) 0 0 n hn k

variable {s e : ℕ} (ar : ℕ → ℕ) (label : Fin s) (hlabel : ar label.val=4) (edge : Fin e)

def labels (a b c : K) (n k : ℕ) : Labelling (D.blockChain a b c n k).shape s e ar where
  vertex _ := label
  vertex_arity j := hlabel.trans (D.blockChain_arity a b c n k j).symm
  edge _ := edge

theorem compile_literal (a b c : K) (n k : ℕ) :
    compile label.val edge.val n k=(labels ar label hlabel edge a b c n k).template := by
  rw [compile,←blockChain_shape_same a b c n k]
  simp [T.shapeTemplate,labels,Labelling.template]

include hlabel in
theorem valid (n k : ℕ) : (compile label.val edge.val n k).WellFormed s e ar := by
  rw [compile_literal ar label hlabel edge (0 : ℚ) 0 0 n k]
  exact (labels ar label hlabel edge (0 : ℚ) 0 0 n k).wellFormed

theorem literal_denote [CharZero K] (a b c : K) (n k : ℕ) (hn : 0<n)
    (G : (i : Fin s) → Signature K (ar i.val)) (X : Fin e → Kernel K)
    (hq : (⟨ar label.val,G label⟩ : AnySignature K)=⟨4,ThreeModeSignatures.original a b c⟩)
    (hX : X edge=Signature.disequality) :
    (((labels ar label hlabel edge a b c n k).template).network
      (labels ar label hlabel edge a b c n k).wellFormed G X).denote=
      ThreeModeSignatures.spectral ((D.A a b n)^(k+1))
        ((D.B a b n+D.C c n)^(k+1)) ((D.B a b n-D.C c n)^(k+1)) := by
  rw [←D.blockChain_denote a b c n hn k]
  apply Labelling.denote_template_of_labels
  · intro j x
    change G label (fun i=>x (Fin.cast (hlabel.trans (D.blockChain_arity a b c n k j).symm) i))=
      (D.blockChain a b c n k).vertex j x
    apply Chain.signature_cast_apply
    exact hq.trans (D.blockChain_signature a b c n k j).symm
  · intro j x y
    exact congrFun₂ (hX.trans (D.blockChain_native a b c n k j).symm) x y

theorem denote [CharZero K] (a b c : K) (n k : ℕ) (hn : 0<n)
    (G : (i : Fin s) → Signature K (ar i.val)) (X : Fin e → Kernel K)
    (hq : (⟨ar label.val,G label⟩ : AnySignature K)=⟨4,ThreeModeSignatures.original a b c⟩)
    (hX : X edge=Signature.disequality) :
    ((compile label.val edge.val n k).network (valid ar label hlabel edge n k) G X).denote=
      ThreeModeSignatures.spectral ((D.A a b n)^(k+1))
        ((D.B a b n+D.C c n)^(k+1)) ((D.B a b n-D.C c n)^(k+1)) := by
  have he := Chain.template_denote_heq _ _ (valid ar label hlabel edge n k)
    (labels ar label hlabel edge a b c n k).wellFormed
    (compile_literal ar label hlabel edge a b c n k) G X
  exact (eq_of_heq he).trans (literal_denote ar label hlabel edge a b c n k hn G X hq hX)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStageTemplate
