import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleNormalize
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleChoice

/-! Unconditional original-row supply of a non-Product ordinary CSP resource.
The block has at most sixteen literal original rows and even incidence at
all free and constant ports. Its coefficients remain in the original field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleChoice
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace O
export GeneralEOPairedFamilyExtractionPhaseOccurrences (rawPorts occurrences)
end O
namespace S
export OrdinaryNegativeNonproductBundleSupport (extract)
end S
namespace N
export OrdinaryNegativeNonproductBundleNormalize (rows rows_length coefficient even_ports nonproduct)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}

def duplicate : List (Fin n→Bool ⊕ Fin n) := [Sum.inr,Sum.inr]

theorem duplicate_value {K : Type*} [CommMonoid K] (f : Signature K n) (x : Fin n→Bool) :
    B.evaluate f duplicate x=f x^2 := by
  simp only [B.evaluate,duplicate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  change f x*f x=f x^2
  exact (pow_two _).symm

theorem duplicate_even (q : Bool ⊕ Fin n) : Even ((O.rawPorts (duplicate (n:=n))).count q) := by
  simp only [O.rawPorts,duplicate,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append]
  exact ⟨_,rfl⟩

/-- Arbitrary support and arbitrary arity, including all signs and fixed
components. The successful non-Product block is selected internally. -/
theorem exists_rows (f : Signature AlgebraicComplex n) (hn : ¬Product f) :
    ∃ps : List (Fin n→Bool ⊕ Fin n),ps.length≤16 ∧
      (∀q : Bool ⊕ Fin n,Even ((O.rawPorts ps).count q)) ∧ ¬Product (B.evaluate f ps) := by
  by_cases hs : Product (fun x=>f x^2)
  · let D := S.extract f hn hs
    exact ⟨N.rows D,by rw [N.rows_length],N.even_ports D,N.nonproduct D⟩
  · refine ⟨duplicate,by simp [duplicate],duplicate_even,?_⟩
    simpa only [show B.evaluate f duplicate=(fun x=>f x^2) from funext (duplicate_value f)] using hs

variable (K : IntermediateField ℚ AlgebraicComplex) (f : Signature K n)

structure Choice where
  rows : List (Fin n→Bool ⊕ Fin n)
  length : rows.length≤16
  even : ∀q : Bool ⊕ Fin n,Even ((O.rawPorts rows).count q)
  nonproduct : ¬Product (fun x=>((B.evaluate f rows x : K) : AlgebraicComplex))

theorem exists_choice (hn : ¬Product (fun x=>(f x : AlgebraicComplex))) : Nonempty (Choice K f) := by
  obtain ⟨ps,hl,he,hp⟩ := exists_rows (fun x=>(f x : AlgebraicComplex)) hn
  refine ⟨⟨ps,hl,he,?_⟩⟩
  simpa only [OrdinaryNegativePhaseBundleChoice.coe_evaluate] using hp

def choose (hn : ¬Product (fun x=>(f x : AlgebraicComplex))) : Choice K f :=
  Classical.choice (exists_choice K f hn)

namespace Choice
variable {K f}

/-- This is an actual fixed positive product over K, without scalar division. -/
def coefficient (D : Choice K f) : Signature K n := B.evaluate f D.rows

theorem even_occurrences (D : Choice K f) (i : Fin n) : Even (O.occurrences D.rows i) :=
  D.even (.inr i)

end Choice
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleChoice
end
