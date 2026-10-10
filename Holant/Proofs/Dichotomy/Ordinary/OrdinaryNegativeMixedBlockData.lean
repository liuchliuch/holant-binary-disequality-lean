import Holant.Proofs.Hardness.GeneralEOPairedFamilyBundleValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilyPrivateValue
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleSemantics

/-! Finite mixed-label literal CSP blocks. The ordinary source format uses
the existing heterogeneous flat CSP codec; canonical pairings provide only
its arity metadata and do not assert any EO field or incidence translation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockData
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace C
export GeneralEOPairedCSPFamilyRaw (Raw Input inputEncoding encoding value)
end C
namespace B
export GeneralEOPairedFamilyBundleRaw (Node Recipe data dataComputes factor row rowFor query)
export GeneralEOPairedFamilyBundleValue (coefficient data_length query_valid query_value)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def pairing (n : ℕ) : OrientedPerfectPairing (n*2) where
  count := n
  ports := (Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finProdFinEquiv

def family (u : ℕ) (a : ℕ→ℕ) : (i : Fin u)→OrientedPerfectPairing ((fun i=>a i*2) i.val) :=
  fun i=>pairing (a i.val)

variable {u s : ℕ} {a b : ℕ→ℕ}
abbrev Node (i : Fin u) := B.Node (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (family u a) (family s b) i
abbrev Recipe := B.Recipe (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (family u a) (family s b)
abbrev Input := C.Input (s:=u) (arity:=fun k=>a k*2) (family u a)
abbrev inputEncoding := C.inputEncoding (s:=u) (arity:=fun k=>a k*2) (family u a)

def ports (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b)) (i : Fin u) : List (Bool ⊕ Fin (a i.val)) :=
  (recipe i).flatMap (fun node=>List.ofFn node.2)

def EvenRecipe (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b)) : Prop :=
  ∀i : Fin u,∀q : Bool ⊕ Fin (a i.val),Even ((ports recipe i).count q)

def factor (row : Fin s×List ℕ) : Factor := (row.1.val,row.2)
def guards (p₀ p₁ : Fin s) : List Factor := OrdinaryNegativePhaseBundleRaw.guards p₀.val p₁.val

def raw (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b)) (p₀ p₁ : Fin s) (r : C.Raw u) : Raw :=
  ⟨r.variables+2,(B.data (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (family u a) (family s b) recipe r).map factor++guards p₀ p₁⟩

def coefficient {K : Type} [CommSemiring K]
    (H : (j : Fin s)→Signature K (b j.val)) (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b)) :
    (i : Fin u)→Signature K (a i.val) :=
  B.coefficient (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (family u a) (family s b) recipe H

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockData
end
