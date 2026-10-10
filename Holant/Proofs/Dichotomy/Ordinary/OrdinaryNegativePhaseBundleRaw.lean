import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinarySquareProgramme
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCore
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseOccurrences
import Holant.Proofs.CountingMachines.CircuitNative.GateAlphabet
import Holant.EightVertex.ProductAnchor.NetworksData

/-! Literal block substitution for the cubic-sign phase source. Two new
addresses carry the constants; every constant occurrence has its own matching
pin occurrence. Equality and pin rows are duplicated. This makes every target
occurrence even without squaring the extracted cubic phase. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleRaw
open Holant Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences
  (rawPorts occurrences)
end O
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
open OrdinaryNegativeCubicCore (cubic)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def sourceArity : ℕ→ℕ
  | 0 => 3
  | 1 => 4
  | _+2 => 1

def sourceRows {K : Type*} [Zero K] [One K] [Neg K] (i : Fin 4) :
    Signature K (sourceArity i.val) :=
  match i with
  | ⟨0,_⟩ => cubic
  | ⟨1,_⟩ => Holant.EightVertex.ProductAnchor.equalityFour
  | ⟨2,_⟩ => Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false
  | ⟨3,_⟩ => Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true
  | ⟨k+4,h⟩ => False.elim (by omega)

abbrev Source := StableHigherCurrentOrdinarySquareProgramme.Input 4 sourceArity
abbrev sourceEncoding := StableHigherCurrentOrdinarySquareProgramme.inputEncoding 4 sourceArity

variable {n : ℕ}
def address (scope : List ℕ) : Bool ⊕ Fin 3→ℕ
  | .inl false => 0
  | .inl true => 1
  | .inr k => scope.getD k.val 0+2

def constantAddresses (ps : List (Fin n→Bool ⊕ Fin 3)) : List ℕ :=
  (O.rawPorts ps).filterMap (fun p=>match p with
    | .inl false=>some 0
    | .inl true=>some 1
    | .inr _=>none)

def constantRows (p₀ p₁ : ℕ) (ps : List (Fin n→Bool ⊕ Fin 3)) : List Factor :=
  (constantAddresses ps).map (fun k=>(if k=0 then p₀ else p₁,[k]))

def phaseRows (j : ℕ) (ps : List (Fin n→Bool ⊕ Fin 3)) (scope : List ℕ) : List Factor :=
  ps.map (fun p=>(j,List.ofFn (fun k=>address scope (p k))))

def block (j e p₀ p₁ : ℕ) (ps : List (Fin n→Bool ⊕ Fin 3)) (row : Factor) : List Factor :=
  if row.1=0 then phaseRows j ps row.2++constantRows p₀ p₁ ps
  else let label := if row.1=1 then e else if row.1=2 then p₀ else p₁
       let target := (label,row.2.map (·+2))
       [target,target]

def guards (p₀ p₁ : ℕ) : List Factor := [(p₀,[0]),(p₀,[0]),(p₁,[1]),(p₁,[1])]

def raw (j e p₀ p₁ : ℕ) (ps : List (Fin n→Bool ⊕ Fin 3)) (r : Raw) : Raw :=
  ⟨r.variables+2,r.factors.flatMap (block j e p₀ p₁ ps)++guards p₀ p₁⟩

def copies (r : Raw) : ℕ := (r.factors.filter (fun row=>row.1=0)).length

@[simp] theorem raw_variables (j e p₀ p₁ : ℕ) (ps : List (Fin n→Bool ⊕ Fin 3)) (r : Raw) :
    (raw j e p₀ p₁ ps r).variables=r.variables+2 := rfl

theorem phase_addresses (j : ℕ) (ps : List (Fin n→Bool ⊕ Fin 3)) (scope : List ℕ) :
    (phaseRows j ps scope).flatMap Prod.snd=(O.rawPorts ps).map (address scope) := by
  simp only [phaseRows,List.flatMap_map,Function.comp_def,O.rawPorts,List.map_flatMap,List.map_ofFn]

theorem constant_addresses (p₀ p₁ : ℕ) (ps : List (Fin n→Bool ⊕ Fin 3)) :
    (constantRows p₀ p₁ ps).flatMap Prod.snd=constantAddresses ps := by
  simp [constantRows,List.flatMap_map]

theorem constant_lt_two (ps : List (Fin n→Bool ⊕ Fin 3)) (k : ℕ)
    (hk : k∈constantAddresses ps) : k<2 := by
  obtain ⟨p,_,hp⟩ := List.mem_filterMap.mp hk
  cases p with
  | inl b => cases b <;> simp at hp <;> omega
  | inr i => simp at hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleRaw
end
