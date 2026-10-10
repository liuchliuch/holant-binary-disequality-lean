import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource

/-! The original-G ordinary source is an exact instance of the universal
controlled target. Every table, coefficient field, literal resource and
length-controlled programme is retained definitionally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledOrdinaryData
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)

def data : NoIOrdinaryRaw.GenericOrdinarySource.Data (PaperControlledHardness.originalTarget G) where
  K:=src.K
  degree:=src.degree
  F:=src.F
  size:=src.size
  b:=src.b
  H:=src.H
  e:=src.e
  p:=src.p
  he:=src.he
  hp:=src.hp
  toOriginal:=src.toOriginal

theorem family_eq : NoIOrdinaryRaw.GenericOrdinarySource.family
    (PaperControlledHardness.originalTarget G) (data G src)=GenericOrdinarySource.family G src :=rfl

def literalX (source : GenericLiteralXSource.Data G) :=
  data G (GenericOrdinarySource.ofLiteralX G source)

theorem literalX_family (source : GenericLiteralXSource.Data G) :
    NoIOrdinaryRaw.GenericOrdinarySource.family (PaperControlledHardness.originalTarget G)
      (literalX G source)=GenericLiteralXSource.family G source :=rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledOrdinaryData
end
