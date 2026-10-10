import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDTable
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionTensor
import Holant.Proofs.CountingMachines.Interface
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators

/-! Literal binary-minor queries. Every old address is retained; the two fresh
addresses at the end of the declared variable block carry the actual pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorRaw
open Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export BinaryCSPProgrammeCore (Raw encoding edgeEncoding edgesEncoding unary variablesComputes edgesComputes)
end C
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace E
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction (Raw Factor)
namespace Raw
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw (factorEncoding encoding)
end Raw
end E
namespace O
export StableHigherCurrentOrdinarySquare (Valid)
export StableHigherCurrentOrdinarySquareProgramme (Input inputEncoding)
end O
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (succComputes)
end W
namespace Access
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons list₁)
end Access
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}
def address (v : ℕ) (e : ℕ×ℕ) : Bool ⊕ Fin 2 → ℕ
  | .inl b => if b then v+1 else v
  | .inr k => if k=0 then e.1 else e.2

def row (j : ℕ) (q : Fin n→Bool ⊕ Fin 2) (v : ℕ) (e : ℕ×ℕ) : E.Factor :=
  (j,List.ofFn (fun k=>address v e (q k)))
def raw (j p₀ p₁ : ℕ) (q : Fin n→Bool ⊕ Fin 2) (r : C.Raw) : E.Raw :=
  ⟨r.variables+2,(p₀,[r.variables])::(p₁,[r.variables+1])::r.edges.map (row j q r.variables)⟩

abbrev contextEncoding := pairEncoding C.unary C.edgeEncoding
abbrev scopeEncoding := framedListEncoding encodingNatBool
abbrev factorsEncoding := framedListEncoding E.Raw.factorEncoding

def addressComputes (p : Bool ⊕ Fin 2) : Computes contextEncoding encodingNatBool
    (fun x=>address x.1 x.2 p) := by
  cases p with
  | inl b =>
      cases b
      · exact (Wiring.firstComputes C.unary C.edgeEncoding).andThen UnaryBinary.computes
      · exact ((Wiring.firstComputes C.unary C.edgeEncoding).andThen W.succComputes).andThen
          UnaryBinary.computes
  | inr k =>
      by_cases h : k=0
      · exact congrComputes ((Wiring.secondComputes C.unary C.edgeEncoding).andThen
          (Wiring.firstComputes encodingNatBool encodingNatBool)) (fun x=>by simp [address,h])
      · exact congrComputes ((Wiring.secondComputes C.unary C.edgeEncoding).andThen
          (Wiring.secondComputes encodingNatBool encodingNatBool)) (fun x=>by simp [address,h])

def rowComputes (j : ℕ) (q : Fin n→Bool ⊕ Fin 2) :
    Computes contextEncoding E.Raw.factorEncoding (fun x=>row j q x.1 x.2) := by
  let scope := congrComputes (fixedListComputes contextEncoding encodingNatBool
    (fun x k=>address x.1 x.2 (q k)) (fun k=>addressComputes (q k)) (List.finRange n))
    (fun _=>List.ofFn_eq_map.symm)
  exact recode (pairComputes (constantComputes contextEncoding encodingNatBool j) scope)
    id (fun _=>rfl) (fun _=>rfl)

def pinComputes (p : ℕ) (b : Bool) : Computes C.encoding E.Raw.factorEncoding
    (fun r=>(p,[if b then r.variables+1 else r.variables])) := by
  let v : Computes C.encoding encodingNatBool (fun r=>if b then r.variables+1 else r.variables) := by
    cases b
    · exact C.variablesComputes.andThen UnaryBinary.computes
    · exact (C.variablesComputes.andThen W.succComputes).andThen UnaryBinary.computes
  exact recode (pairComputes (constantComputes C.encoding encodingNatBool p)
    (Access.list₁ encodingNatBool v)) id (fun _=>rfl) (fun _=>rfl)

def rawComputes (j p₀ p₁ : ℕ) (q : Fin n→Bool ⊕ Fin 2) :
    Computes C.encoding E.Raw.encoding (raw j p₀ p₁ q) := by
  let rows := (pairComputes C.variablesComputes C.edgesComputes).andThen
    (mapListComputes C.unary C.edgeEncoding E.Raw.factorEncoding (row j q) (rowComputes j q))
  let tail := (pairComputes (pinComputes p₁ true) rows).andThen (Access.cons E.Raw.factorEncoding)
  let factors := (pairComputes (pinComputes p₀ false) tail).andThen (Access.cons E.Raw.factorEncoding)
  exact recode (pairComputes ((C.variablesComputes.andThen W.succComputes).andThen W.succComputes)
    factors) id (fun _=>rfl) (fun _=>rfl)

variable {s : ℕ} {a : ℕ→ℕ} (j p₀ p₁ : Fin s) (q : Fin (a j.val)→Bool ⊕ Fin 2)

theorem raw_valid (h₀ : a p₀.val=1) (h₁ : a p₁.val=1) (r : P.Input) :
    O.Valid s a (raw j.val p₀.val p₁.val q r.val) := by
  intro t ht
  simp only [raw,List.mem_cons,List.mem_map] at ht
  rcases ht with rfl | rfl | ⟨e,he,rfl⟩
  · exact ⟨p₀.isLt,by simpa using h₀.symm,by intro k hk; simp only [List.mem_singleton] at hk; subst k; simp [raw]⟩
  · exact ⟨p₁.isLt,by simpa using h₁.symm,by intro k hk; simp only [List.mem_singleton] at hk; subst k; simp [raw]⟩
  · refine ⟨j.isLt,by simp [row],?_⟩
    intro k hk
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
    have he' := r.property.1 e he
    cases hq : q i with
    | inl b => cases b <;> simp [raw,address]
    | inr k => simp only [address]; split_ifs <;> simp only [raw] <;> omega

def query (h₀ : a p₀.val=1) (h₁ : a p₁.val=1) (r : P.Input) : O.Input s a :=
  ⟨raw j.val p₀.val p₁.val q r.val,raw_valid j p₀ p₁ q h₀ h₁ r⟩

def queryComputes (h₀ : a p₀.val=1) (h₁ : a p₁.val=1) :
    Computes P.inputEncoding (O.inputEncoding s a) (query j p₀ p₁ q h₀ h₁) :=
  recode (rawComputes j.val p₀.val p₁.val q) Subtype.val (fun _=>rfl) (fun _=>rfl)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorRaw
end
