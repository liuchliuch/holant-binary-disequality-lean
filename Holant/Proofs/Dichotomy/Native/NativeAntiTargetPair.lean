import Holant.Proofs.Dichotomy.Native.NativeAntiTargetExtension
import Holant.Proofs.Closure.ProgrammeCompose

/-! Two independently requested antidiagonal rows share one original-field
native-X source. The second interpolation uses the retained original graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetPair
open Holant Holant.Algebraic Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export NativeAntiTargetSource (Output base)
end S
namespace E
export NativeAntiTargetExtension (Extension produce relabel)
end E
namespace A
export NativeAntiTargetAlgebra (anti)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
structure Extension (first second : K) where
  count : ℕ
  b : ℕ→ℕ
  table : (i : Fin count)→Signature K (b i.val)
  old : Fin s→Fin count
  old_literal : ∀i,(⟨b (old i).val,table (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩
  left : Fin count
  right : Fin count
  left_literal : (⟨b left.val,table left⟩ : AnySignature K)=⟨2,binarySignature (A.anti 1 first)⟩
  right_literal : (⟨b right.val,table right⟩ : AnySignature K)=⟨2,binarySignature (A.anti 1 second)⟩
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((S.base table F).evaluate F) ((S.base H F).evaluate F)

variable (N : S.Output H 2) (p q first second : K) (hp : p≠0) (hq : q≠0)
variable (infinite : ∀k : ℕ,0<k→(q/p)^k≠1)
variable (form : N.network.denote=binarySignature (A.anti p q))
def produce : Extension H F first second := by
  let L:=E.produce H F N p q first hp hq infinite form
  let NN:=E.relabel H L.table L.old L.old_literal N
  let R:=E.produce L.table F NN p q second hp hq infinite form
  exact {
    count:=R.count
    b:=R.b
    table:=R.table
    old:=R.old ∘ L.old
    old_literal:=fun i=>(R.old_literal (L.old i)).trans (L.old_literal i)
    left:=R.old L.label
    right:=R.label
    left_literal:=(R.old_literal L.label).trans L.literal
    right_literal:=R.literal
    source:=Programme.compose R.source L.source }

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetPair
end
