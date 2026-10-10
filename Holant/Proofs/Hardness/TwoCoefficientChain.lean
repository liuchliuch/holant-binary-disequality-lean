import Holant.Proofs.Hardness.TwoCoefficientStage
import Holant.Proofs.Hardness.ExactTwoChainRecords

/-! Actual long chains for aE+bB, using the same ordered two-X-edge series
and the exact existing serialized chain templates. No query compiler is changed.
The k-th chain has k+1 original weighted vertices and 2k native-X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientChain
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export ExactTwoChain (series)
end C
namespace S
export TwoCoefficientSignatures (weighted linear)
export ExactTwoSignatures (E B)
end S
namespace T
export ExactTwoChainTemplate (shapeTemplate series_shape_independent compile)
end T
namespace R
export ExactTwoChainRecords (explicitTemplate valid compile_eq)
end R
namespace Cast
export Holant.Complexity.BinaryInterpolation.Chains (signature_cast_apply template_denote_heq)
end Cast
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

def network (u v : K) : ℕ → Network K 4
  | 0 => Network.corolla (S.weighted u v)
  | k+1 => C.series (network u v k) (Network.corolla (S.weighted u v))

theorem network_denote (u v : K) (k : ℕ) :
    (network u v k).denote=S.weighted (u^(k+1)) (v*(2*v)^k) := by
  induction k with
  | zero => simp [network,Network.denote_corolla]
  | succ k ih =>
      rw [network,TwoCoefficientStage.series_weighted _ _ _ _ _ _ ih (Network.denote_corolla _)]
      congr 1 <;> simp only [pow_succ] <;> ring

theorem counts (u v : K) (k : ℕ) :
    (network u v k).shape.vertices=k+1 ∧ (network u v k).shape.edges=2*k := by
  induction k with
  | zero => constructor <;> rfl
  | succ k ih =>
      change (network u v k).shape.vertices+1=k+1+1 ∧
        ((network u v k).shape.edges+0+1)+1=2*(k+1)
      omega

theorem signature (u v : K) (k : ℕ) (j : Fin (network u v k).shape.vertices) :
    (⟨(network u v k).shape.arity j,(network u v k).vertex j⟩ : AnySignature K)=⟨4,S.weighted u v⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (⟨(Network.tensorFinite (network u v k) (Network.corolla (S.weighted u v))).arity (finSumFinEquiv.symm j),
        (Network.tensorFinite (network u v k) (Network.corolla (S.weighted u v))).vertex (finSumFinEquiv.symm j)⟩ : AnySignature K)=_
      cases finSumFinEquiv.symm j with
      | inl j => exact ih j
      | inr j => rfl

theorem arity (u v : K) (k : ℕ) (j : Fin (network u v k).shape.vertices) :
    (network u v k).shape.arity j=4 := congrArg Sigma.fst (signature u v k j)

theorem native (u v : K) (k : ℕ) : ∀e,(network u v k).edge e=Signature.disequality := by
  induction k with
  | zero => intro e; exact Fin.elim0 e
  | succ k ih =>
      intro e
      refine Fin.cases rfl (fun e=>?_) e
      refine Fin.cases rfl (fun e=>?_) e
      change Sum.elim (network u v k).edge (Network.corolla (S.weighted u v)).edge (finSumFinEquiv.symm e)=_
      cases finSumFinEquiv.symm e with
      | inl e => exact ih e
      | inr e => exact Fin.elim0 e

theorem shape_same (u v : K) (k : ℕ) :
    (network u v k).shape=(ExactTwoChain.network (K:=ℚ) k).shape := by
  induction k with
  | zero => rfl
  | succ k ih => exact T.series_shape_independent _ _ _ _ ih rfl

variable {s e : ℕ} (a : ℕ → ℕ) (label : Fin s) (hlabel : a label.val=4) (edge : Fin e)

def labels (u v : K) (k : ℕ) : Labelling (network u v k).shape s e a where
  vertex _ := label
  vertex_arity j := hlabel.trans (arity u v k j).symm
  edge _ := edge

theorem compile_literal (u v : K) (k : ℕ) :
    R.explicitTemplate label.val edge.val k=(labels a label hlabel edge u v k).template := by
  rw [←R.compile_eq,T.compile,←shape_same u v k]
  simp [T.shapeTemplate,labels,Labelling.template]

theorem literal_denote (u v : K) (k : ℕ)
    (G : (i : Fin s) → Signature K (a i.val)) (X : Fin e → Kernel K)
    (hq : (⟨a label.val,G label⟩ : AnySignature K)=⟨4,S.weighted u v⟩)
    (hX : X edge=Signature.disequality) :
    (((labels a label hlabel edge u v k).template).network
      (labels a label hlabel edge u v k).wellFormed G X).denote=
      S.weighted (u^(k+1)) (v*(2*v)^k) := by
  rw [←network_denote u v k]
  apply Labelling.denote_template_of_labels
  · intro j x
    change G label (fun i=>x (Fin.cast (hlabel.trans (arity u v k j).symm) i))=(network u v k).vertex j x
    apply Cast.signature_cast_apply
    exact hq.trans (signature u v k j).symm
  · intro j x y
    exact congrFun₂ (hX.trans (native u v k j).symm) x y

theorem denote (u v : K) (k : ℕ)
    (G : (i : Fin s) → Signature K (a i.val)) (X : Fin e → Kernel K)
    (hq : (⟨a label.val,G label⟩ : AnySignature K)=⟨4,S.weighted u v⟩)
    (hX : X edge=Signature.disequality) :
    ((R.explicitTemplate label.val edge.val k).network (R.valid a label hlabel edge k) G X).denote=
      S.weighted (u^(k+1)) (v*(2*v)^k) := by
  have he := Cast.template_denote_heq _ _ (R.valid a label hlabel edge k)
    (labels a label hlabel edge u v k).wellFormed (compile_literal a label hlabel edge u v k) G X
  exact (eq_of_heq he).trans (literal_denote a label hlabel edge u v k G X hq hX)

theorem normalized [CharZero K] (u v : K) (hv : v≠0) (k : ℕ) :
    S.weighted (u^(k+1)) (v*(2*v)^k)=
      (2*v)^k • (v • S.B+(u/(2*v))^k • (u • S.E)) := by
  rw [S.linear]
  funext x
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,div_pow,pow_succ]
  have h : (2*v)^k≠0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hv)
  field_simp
  <;> ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientChain
