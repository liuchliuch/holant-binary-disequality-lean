import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenDiagonalRaw
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Close an odd-boundary recipe with one marked temporary unary occurrence
per boundary. The temporary row is used only in this compiler's intermediate
closed presentation; the terminal replacement removes every such occurrence. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddRaw
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace D
export OrdinaryNegativeMixedBlockData (ports guards)
export OrdinaryNegativeXUniversalResource (OddResource)
end D
namespace P
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end P
namespace V
export OrdinaryNegativeMixedBlockValidity (even_map)
export OrdinaryNegativePhaseBundleValidity (guards_good guards_even)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s n : ℕ} {a : ℕ→ℕ}
variable (row : D.OddResource (s:=s) a n)

def arity (j : ℕ) : ℕ := if j<s then a j else 1

def address : Bool ⊕ Fin (n+row.privateCount)→ℕ := Sum.elim (fun b=>if b then 1 else 0) (fun i=>i.val+2)

def markers : List (Bool ⊕ Fin (n+row.privateCount)) := List.ofFn (fun j : Fin n=>Sum.inr (Fin.castAdd row.privateCount j))

def markedFactors (_row : D.OddResource (s:=s) a n) : List Factor := List.ofFn (fun j : Fin n=>(s,[j.val+2]))

def factors : List Factor := (row.rows 0).map (fun node=>(node.1.val,List.ofFn (fun i=>address row (node.2 i))))

def paddedPorts := markers row++D.ports row.rows 0

theorem markers_constant (b : Bool) : (markers row).count (.inl b)=0 := by
  rw [markers,P.count_ofFn]
  simp

theorem markers_boundary (j : Fin n) : (markers row).count (.inr (Fin.castAdd row.privateCount j))=1 := by
  rw [markers,P.count_ofFn]
  simp only [Sum.inr.injEq,Fin.castAdd_inj,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem markers_private (j : Fin row.privateCount) : (markers row).count (.inr (Fin.natAdd n j))=0 := by
  rw [markers,P.count_ofFn]
  have ne (i : Fin n) : Fin.castAdd row.privateCount i≠Fin.natAdd n j := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  simp only [Sum.inr.injEq,ne,ite_false,Finset.sum_const_zero]

theorem padded_even (q : Bool ⊕ Fin (n+row.privateCount)) : Even ((paddedPorts row).count q) := by
  rw [paddedPorts,List.count_append]
  cases q with
  | inl b=>rw [markers_constant,zero_add];exact row.constant_even b
  | inr q=>
      refine Fin.addCases (fun j=>?_) (fun j=>?_) q
      · rw [markers_boundary]
        have odd:=row.boundary_odd j
        rcases odd with ⟨k,hk⟩
        exact ⟨k+1,by omega⟩
      · rw [markers_private,zero_add]
        exact row.private_even j

theorem marked_addresses : (markedFactors row).flatMap Prod.snd=
    (markers row).map (address row) := by
  simp only [markedFactors,markers,List.map_ofFn,Function.comp_def,address,Sum.elim_inr,Fin.val_castAdd]
  rw [List.ofFn_eq_map]
  simp only [List.flatMap_map]
  rw [List.ofFn_eq_map]
  induction List.finRange n with
  | nil=>rfl
  | cons j js ih=>simp only [List.flatMap_cons,List.map_cons,List.singleton_append,ih]

theorem factor_addresses : ((markedFactors row)++factors row).flatMap Prod.snd=(paddedPorts row).map (address row) := by
  rw [List.flatMap_append,marked_addresses]
  simp only [factors,paddedPorts,D.ports,List.map_append,
    List.flatMap_map,Function.comp_def,List.map_flatMap,List.map_ofFn]

variable (p0 p1 : Fin s)
def raw : Raw := ⟨(n+row.privateCount)+2,markedFactors row++factors row++D.guards p0 p1⟩

theorem raw_even (i : ℕ) : Even ((raw row p0 p1).degree i) := by
  rw [StableHigherCurrentOrdinarySquare.degree_flat]
  change Even ((((markedFactors row++factors row)++D.guards p0 p1).flatMap Prod.snd).count i)
  rw [List.flatMap_append,List.count_append,factor_addresses]
  exact (V.even_map (paddedPorts row) (padded_even row) (address row) i).add (V.guards_even p0 p1 i)

variable (h0 : a p0.val=1) (h1 : a p1.val=1)
include h0 h1 in
theorem good : ∀factor∈(raw row p0 p1).factors,
    factor.1<s+1 ∧ factor.2.length=arity (s:=s) (a:=a) factor.1 ∧
      ∀i∈factor.2,i<(n+row.privateCount)+2 := by
  intro factor hf
  rcases List.mem_append.mp hf with hf|hf
  · rcases List.mem_append.mp hf with hf|hf
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
      refine ⟨by omega,by simp [arity],?_⟩
      intro i hi
      simp only [List.mem_singleton] at hi
      subst i
      omega
    · obtain ⟨node,_,rfl⟩ := List.mem_map.mp hf
      refine ⟨by have h:=node.1.isLt;omega,?_,?_⟩
      · simp only [List.length_ofFn,arity,ite_eq_left node.1.isLt]
        rfl
      · intro i hi
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
        cases hp : node.2 j with
        | inl bit=>cases bit <;> simp [address]
        | inr q=>
            change q.val+2<(n+row.privateCount)+2
            have hq : q.val<n+row.privateCount := q.isLt
            omega
  · have h:=V.guards_good p0 p1 h0 h1 (n+row.privateCount) factor hf
    exact ⟨Nat.lt_succ_of_lt h.1,by simpa only [arity,ite_eq_left h.1] using h.2.1,h.2.2⟩

include h0 h1 in
theorem valid : (raw row p0 p1).Valid (s+1) (arity (s:=s) (a:=a)) := by
  have hg:=good row p0 p1 h0 h1
  refine ⟨?_,?_,fun i _=>raw_even row p0 p1 i⟩
  · intro v
    have h:=hg _ (List.get_mem _ v)
    exact ⟨h.1,h.2.1⟩
  · intro p
    exact (hg _ (List.get_mem _ p.1)).2.2 _ (List.get_mem _ p.2)

def input : Raw.Input (s+1) (arity (s:=s) (a:=a)) := ⟨raw row p0 p1,valid row p0 p1 h0 h1⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddRaw
end
