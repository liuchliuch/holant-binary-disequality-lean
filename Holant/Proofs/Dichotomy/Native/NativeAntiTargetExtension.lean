import Holant.Proofs.Dichotomy.Native.NativeAntiTargetSource
import Holant.Projective.BoundedTorsion.Group

/-! Same-field native-X extension with literal old rows and the requested
antidiagonal. Positive projective periods are treated by the exact ratio law. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetExtension
open Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace S
export NativeAntiTargetSource (Output base table arity old old_literal label literal source)
end S
namespace A
export NativeAntiTargetAlgebra (anti)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s t degree n : ℕ} {a b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

def relabel (J : (i : Fin t)→Signature K (b i.val)) (old : Fin s→Fin t)
    (literal : ∀i,(⟨b (old i).val,J (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩)
    (N : S.Output H n) : S.Output J n where
  network:=N.network
  labels:={vertex v:=old (N.labels.vertex v)
           vertex_arity v:=(congrArg Sigma.fst (literal (N.labels.vertex v))).trans (N.labels.vertex_arity v)
           edge:=N.labels.edge}
  exact:=fun v=>(literal (N.labels.vertex v)).trans (N.exact v)
  native:=N.native

def row (j : Fin s) (f : Signature K n)
    (literal : (⟨a j.val,H j⟩ : AnySignature K)=⟨n,f⟩) : S.Output H n where
  network:=Network.corolla f
  labels:={vertex _:=j
           vertex_arity _:=congrArg Sigma.fst literal
           edge:=Fin.elim0}
  exact:=fun _=>literal
  native:=fun e=>Fin.elim0 e

theorem infinite_of_not_finite (p q : K) (hp : p≠0)
    (infinite : ¬ProjectivelyFinite (transfer (A.anti p q))) :
    ∀k : ℕ,0<k→(q/p)^k≠1 := by
  intro k hk period
  apply infinite
  refine ⟨k,hk,p^k,pow_ne_zero _ hp,?_⟩
  change (A.anti p q*X)^k=_
  rw [NativeAntiTargetAlgebra.transfer,OrdinaryTargetInterpolationDiagonal.power]
  have he : q^k=p^k := by
    rw [div_pow] at period
    exact (div_eq_one_iff_eq (pow_ne_zero _ hp)).mp period
  ext i j
  cases i <;> cases j <;> simp [OrdinaryTargetInterpolationDiagonal.diagonal,he]

structure Extension (target : K) where
  count : ℕ
  b : ℕ→ℕ
  table : (i : Fin count)→Signature K (b i.val)
  old : Fin s→Fin count
  old_literal : ∀i,(⟨b (old i).val,table (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩
  label : Fin count
  literal : (⟨b label.val,table label⟩ : AnySignature K)=⟨2,binarySignature (A.anti 1 target)⟩
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((S.base table F).evaluate F) ((S.base H F).evaluate F)

variable (N : S.Output H 2) (p q target : K) (hp : p≠0) (hq : q≠0)
variable (infinite : ∀k : ℕ,0<k→(q/p)^k≠1)
variable (form : N.network.denote=binarySignature (A.anti p q))
def produce : Extension H F target where
  count:=s+1
  b:=S.arity H N
  table:=S.table H F N p q target
  old:=S.old
  old_literal:=S.old_literal H F N p q target
  label:=S.label
  literal:=S.literal H F N p q target
  source:=S.source H F N p q target hp hq infinite form


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetExtension
end
