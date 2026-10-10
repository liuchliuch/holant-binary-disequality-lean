import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportExtraction

/-! Internal extraction of the signed ternary XOR-hole witness, followed by
its fixed literal binary pin/projection gadget. No successful support point,
minor, or hardness reduction is supplied by the caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportWitness
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace G
export GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end G
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose substitute_compose)
end I
namespace E
export OrdinaryNegativeAffineSupportExtraction (shift)
end E
namespace S
export OrdinaryNegativeNonclosedSupportExtraction (Three support ternary)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}

def ports (a b c : Fin n→Bool) : Fin n→Bool ⊕ Fin 3 := fun i=>
  if Bool.xor (a i) (b i) then
    if Bool.xor (a i) (c i) then .inr 2 else .inr 0
  else if Bool.xor (a i) (c i) then .inr 1 else .inl false

variable {K : Type*} [Field K] (f : Signature K n)

def ternaryRow (a b c : Fin n→Bool) : Signature K 3 :=
  fun z=>E.shift f a (T.substitute (ports a b c) z)

theorem ternary_values (a b c : Fin n→Bool) :
    ternaryRow f a b c ![false,false,false]=f a ∧
    ternaryRow f a b c ![true,false,true]=f b ∧
    ternaryRow f a b c ![false,true,true]=f c ∧
    ternaryRow f a b c ![true,true,false]=f (tripleXor a b c) := by
  have h (z : Fin 3→Bool) : ternaryRow f a b c z=
      f (fun i=>Bool.xor (a i) (T.substitute (ports a b c) z i)) := rfl
  simp only [h]
  refine ⟨congrArg f ?_,congrArg f ?_,congrArg f ?_,congrArg f ?_⟩
  all_goals
    funext i
    cases ha : a i <;> cases hb : b i <;> cases hc : c i <;>
      simp [ports,T.substitute,tripleXor,ha,hb,hc]

/-- Substitute a ternary literal minor into every occurrence of its selected
binary gadget, retaining every private variable and coefficient exactly. -/
def composeMinor (p : Fin n→Bool ⊕ Fin 3) (q : G.Gadget 3 2) : G.Gadget n 2 :=
  ⟨q.privateCount,q.ports.map (fun r=>I.compose p r)⟩

theorem composeMinor_value (p : Fin n→Bool ⊕ Fin 3) (q : G.Gadget 3 2) (z : Fin 2→Bool) :
    G.denote f (composeMinor p q) z=G.denote (fun x=>f (T.substitute p x)) q z := by
  unfold G.denote composeMinor B.evaluate
  simp only [List.map_map,Function.comp_def,I.substitute_compose]

structure Choice where
  base : Fin n→Bool
  gadget : G.Gadget n 2
  three : S.Three (G.denote (E.shift f base) gadget)

/-- A missing ternary-XOR support word is the only premise. -/
theorem exists_choice (hn : ¬∀a b c,f a≠0→f b≠0→f c≠0→f (tripleXor a b c)≠0) :
    Nonempty (Choice f) := by
  classical
  push_neg at hn
  obtain ⟨a,b,c,ha,hb,hc,hz⟩ := hn
  obtain ⟨h0,h1,h2,h3⟩ := ternary_values f a b c
  obtain ⟨q,hq⟩ := S.ternary (ternaryRow f a b c)
    (by rwa [h0]) (by rwa [h1]) (by rwa [h2]) (by rwa [h3])
  refine ⟨⟨a,composeMinor (ports a b c) q,?_⟩⟩
  have he : G.denote (E.shift f a) (composeMinor (ports a b c) q)=
      G.denote (ternaryRow f a b c) q := by
    funext z
    exact composeMinor_value (E.shift f a) (ports a b c) q z
  rwa [he]

def choose (hn : ¬∀a b c,f a≠0→f b≠0→f c≠0→f (tripleXor a b c)≠0) : Choice f :=
  Classical.choice (exists_choice f hn)

namespace Choice
variable {f}
def coefficient (q : Choice f) : Signature K 2 := G.denote (E.shift f q.base) q.gadget
end Choice

variable (L : IntermediateField ℚ AlgebraicComplex) (g : Signature L 2)

theorem coe_three (h : S.Three g) : S.Three (fun z=>(g z : AlgebraicComplex)) := by
  have he : S.support (fun z=>(g z : AlgebraicComplex))=S.support g := by
    ext z
    simp only [S.support,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hn hz
      exact hn (congrArg (fun v : L=>(v : AlgebraicComplex)) hz)
    · intro hn hz
      exact hn (Subtype.ext hz)
  change (S.support _).card=3
  rwa [he]

theorem nonaffine (h : S.Three g) : ¬Affine (fun z=>(g z : AlgebraicComplex)) :=
  EOBinaryPlaneClassification.three_not_affine _ (by
    simpa only [S.Three,S.support,EOQuaternarySparseTract.support] using coe_three L g h)

theorem nonproduct (h : S.Three g) : ¬Product (fun z=>(g z : AlgebraicComplex)) :=
  EOBinaryPlaneClassification.three_not_product _ (by
    simpa only [S.Three,S.support,EOQuaternarySparseTract.support] using coe_three L g h)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportWitness
end
