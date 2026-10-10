import Holant.Proofs.Hardness.ThreeModeSignatures
import Holant.Proofs.Hardness.ExactTwoChainRecords

/-! Actual three-mode self-dual EO chains. Each chain uses only the original
q table and native X, and compiles to the accepted literal four-port records. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeChain
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export ExactTwoChain (series)
end C
namespace S
export ThreeModeSignatures (original spectral original_spectral spectral_linear)
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

def network (a b c : K) : ℕ → Network K 4
  | 0 => Network.corolla (S.original a b c)
  | k+1 => C.series (network a b c k) (Network.corolla (S.original a b c))

theorem series_spectral [CharZero K] (N M : Network K 4) (u v w p q r : K)
    (hN : N.denote=S.spectral u v w) (hM : M.denote=S.spectral p q r) :
    (C.series N M).denote=S.spectral (u*p) (v*q) (w*r) := by
  funext x
  rw [ExactTwoChain.series_denote,hN,hM]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.spectral,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      h0,h1,h2,h3] <;> ring

theorem network_denote [CharZero K] (a b c : K) (k : ℕ) :
    (network a b c k).denote=S.spectral (c^(k+1)) ((a+b)^(k+1)) ((b-a)^(k+1)) := by
  induction k with
  | zero => simp [network,Network.denote_corolla,S.original_spectral]
  | succ k ih =>
      rw [network,series_spectral _ _ _ _ _ _ _ _ ih
        ((Network.denote_corolla _).trans (S.original_spectral a b c))]
      simp only [pow_succ]

theorem counts (a b c : K) (k : ℕ) :
    (network a b c k).shape.vertices=k+1 ∧ (network a b c k).shape.edges=2*k := by
  induction k with
  | zero => constructor <;> rfl
  | succ k ih =>
      change (network a b c k).shape.vertices+1=k+1+1 ∧
        ((network a b c k).shape.edges+0+1)+1=2*(k+1)
      omega

theorem signature (a b c : K) (k : ℕ) (j : Fin (network a b c k).shape.vertices) :
    (⟨(network a b c k).shape.arity j,(network a b c k).vertex j⟩ : AnySignature K)=⟨4,S.original a b c⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (⟨(Network.tensorFinite (network a b c k) (Network.corolla (S.original a b c))).arity (finSumFinEquiv.symm j),
        (Network.tensorFinite (network a b c k) (Network.corolla (S.original a b c))).vertex (finSumFinEquiv.symm j)⟩ : AnySignature K)=_
      cases finSumFinEquiv.symm j with
      | inl j => exact ih j
      | inr j => rfl

theorem arity (a b c : K) (k : ℕ) (j : Fin (network a b c k).shape.vertices) :
    (network a b c k).shape.arity j=4 := congrArg Sigma.fst (signature a b c k j)

theorem native (a b c : K) (k : ℕ) : ∀e,(network a b c k).edge e=Signature.disequality := by
  induction k with
  | zero => intro e; exact Fin.elim0 e
  | succ k ih =>
      intro e
      refine Fin.cases rfl (fun e=>?_) e
      refine Fin.cases rfl (fun e=>?_) e
      change Sum.elim (network a b c k).edge (Network.corolla (S.original a b c)).edge (finSumFinEquiv.symm e)=_
      cases finSumFinEquiv.symm e with
      | inl e => exact ih e
      | inr e => exact Fin.elim0 e

theorem shape_same (a b c : K) (k : ℕ) :
    (network a b c k).shape=(ExactTwoChain.network (K:=ℚ) k).shape := by
  induction k with
  | zero => rfl
  | succ k ih => exact T.series_shape_independent _ _ _ _ ih rfl

variable {s e : ℕ} (ar : ℕ → ℕ) (label : Fin s) (hlabel : ar label.val=4) (edge : Fin e)

def labels (a b c : K) (k : ℕ) : Labelling (network a b c k).shape s e ar where
  vertex _ := label
  vertex_arity j := hlabel.trans (arity a b c k j).symm
  edge _ := edge

theorem compile_literal (a b c : K) (k : ℕ) :
    R.explicitTemplate label.val edge.val k=(labels ar label hlabel edge a b c k).template := by
  rw [←R.compile_eq,T.compile,←shape_same a b c k]
  simp [T.shapeTemplate,labels,Labelling.template]

theorem literal_denote [CharZero K] (a b c : K) (k : ℕ)
    (G : (i : Fin s) → Signature K (ar i.val)) (X : Fin e → Kernel K)
    (hq : (⟨ar label.val,G label⟩ : AnySignature K)=⟨4,S.original a b c⟩)
    (hX : X edge=Signature.disequality) :
    (((labels ar label hlabel edge a b c k).template).network
      (labels ar label hlabel edge a b c k).wellFormed G X).denote=
      S.spectral (c^(k+1)) ((a+b)^(k+1)) ((b-a)^(k+1)) := by
  rw [←network_denote a b c k]
  apply Labelling.denote_template_of_labels
  · intro j x
    change G label (fun i=>x (Fin.cast (hlabel.trans (arity a b c k j).symm) i))=(network a b c k).vertex j x
    apply Cast.signature_cast_apply
    exact hq.trans (signature a b c k j).symm
  · intro j x y
    exact congrFun₂ (hX.trans (native a b c k j).symm) x y

theorem denote [CharZero K] (a b c : K) (k : ℕ)
    (G : (i : Fin s) → Signature K (ar i.val)) (X : Fin e → Kernel K)
    (hq : (⟨ar label.val,G label⟩ : AnySignature K)=⟨4,S.original a b c⟩)
    (hX : X edge=Signature.disequality) :
    ((R.explicitTemplate label.val edge.val k).network (R.valid ar label hlabel edge k) G X).denote=
      S.spectral (c^(k+1)) ((a+b)^(k+1)) ((b-a)^(k+1)) := by
  have he := Cast.template_denote_heq _ _ (R.valid ar label hlabel edge k)
    (labels ar label hlabel edge a b c k).wellFormed (compile_literal ar label hlabel edge a b c k) G X
  exact (eq_of_heq he).trans (literal_denote ar label hlabel edge a b c k G X hq hX)

/-- The negative sign on Bminus follows from the actual two-X contraction. -/
theorem chain_law [CharZero K] (a b c : K) (k : ℕ) :
    (network a b c k).denote=c^(k+1) • S.E+
      (a+b)^(k+1) • ((1/2 : K) • S.B)+
      (b-a)^(k+1) • ((-1/2 : K) • SignedTwoCoefficientSignatures.Bminus) := by
  rw [network_denote,S.spectral_linear]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeChain
