import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMinimalRank
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockConstants
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockParityCompose
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource

/-! Remove actual pure pinnings from a heterogeneous even recipe. Each pinned
row is replaced by one unchanged original row and literal matching constant
pins. Every free port occurs once, every constant port occurs evenly, and
composition retains the exact coefficient and all private sums. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPurePins
open Holant
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseMinimalRank (PurePins)
end P
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences
  (count_ofFn rawPorts occurrences)
end O
namespace C
export OrdinaryNegativeMixedBlockConstants
  (complete ports_complete constants_count_left constants_count_right coefficient_complete)
end C
namespace M
export OrdinaryNegativeMixedBlockCompose (compose coefficient_compose)
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace Q
export OrdinaryNegativeMixedBlockParityCompose (OddInterface even_compose)
end Q
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

/-- A pure pinning has exactly one original occurrence of every exposed port. -/
theorem pure_count {m n : ℕ} (p : Fin n→Bool ⊕ Fin m) (hp : P.PurePins p) (i : Fin m) :
    (List.ofFn p).count (Sum.inr i)=1 := by
  obtain ⟨j,hj,unique⟩ := hp i
  rw [O.count_ofFn,Finset.sum_eq_single j]
  · simp [hj]
  · intro q _ hq
    have he : p q≠Sum.inr i := fun h=>hq (unique q h)
    simp [he]
  · simp

theorem occurrences_single {m n : ℕ} (p : Fin n→Bool ⊕ Fin m) (hp : P.PurePins p) (i : Fin m) :
    O.occurrences [p] i=1 := by
  simpa only [O.occurrences,O.rawPorts,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    using pure_count p hp i

variable {u v s : ℕ} {a b c : ℕ→ℕ}
variable (labels : Fin v→Fin s)
variable (p : (i : Fin v)→Fin (c (labels i).val)→Bool ⊕ Fin (b i.val))
variable (hp : ∀i,P.PurePins (p i))
variable (pins : Bool→Fin s) (arity : ∀q,c (pins q).val=1)

def base : Recipe (u:=v) (s:=s) (a:=b) (b:=c) := fun i=>[⟨labels i,p i⟩]
def inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c) := C.complete pins (base labels p)

theorem base_ports (i : Fin v) : ports (base labels p) i=List.ofFn (p i) := by
  simp [ports,base]

include hp arity in
theorem odd_interface : Q.OddInterface (inner labels p pins) := by
  constructor
  · intro i q
    rw [inner,C.ports_complete pins arity,List.count_append,C.constants_count_left]
    exact ⟨_,rfl⟩
  · intro i j
    rw [inner,C.ports_complete pins arity,List.count_append,C.constants_count_right,
      Nat.add_zero,base_ports,pure_count (p i) (hp i)]
    decide

def recipe (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b)) :
    Recipe (u:=u) (s:=s) (a:=a) (b:=c) := M.compose outer (inner labels p pins)

include hp arity in
theorem even_recipe (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b)) (ho : EvenRecipe outer) :
    EvenRecipe (recipe labels p pins outer) :=
  Q.even_compose outer (inner labels p pins) ho (odd_interface labels p hp pins arity)

variable {K : Type} [Field K] (H : (j : Fin s)→Signature K (c j.val))
variable (literal : ∀q,(⟨c (pins q).val,H (pins q)⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin q⟩)

def rows (i : Fin v) : Signature K (b i.val) := fun x=>H (labels i) (T.substitute (p i) x)

include literal in
theorem inner_value (i : Fin v) (x : Fin (b i.val)→Bool) :
    coefficient H (inner labels p pins) i x=rows labels p H i x := by
  rw [inner,C.coefficient_complete pins H literal]
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    base,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rfl

include literal in
theorem coefficient_eq (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (i : Fin u) (x : Fin (a i.val)→Bool) :
    coefficient H (recipe labels p pins outer) i x=coefficient (rows labels p H) outer i x := by
  rw [recipe,M.coefficient_compose]
  have he : coefficient H (inner labels p pins)=rows labels p H := by
    funext i x
    exact inner_value labels p pins H literal i x
  rw [he]

include literal in
theorem trace_eq (k : ℕ) (outer : Recipe (u:=u) (s:=v) (a:=fun i=>a i+k) (b:=b))
    (i : Fin u) (x : Fin (a i.val)→Bool) :
    M.trace H k (recipe labels p pins outer) i x=M.trace (rows labels p H) k outer i x := by
  unfold M.trace
  apply Finset.sum_congr rfl
  intro y _
  exact coefficient_eq labels p pins H literal outer i (Fin.addCases x y)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPurePins
end
