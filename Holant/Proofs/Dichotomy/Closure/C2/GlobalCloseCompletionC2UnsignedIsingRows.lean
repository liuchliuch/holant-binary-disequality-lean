import Holant.Proofs.Hardness.BinaryIsingRows

/-! The saved signed-apex interpolation can query unsigned Ising instead:
swap its two weights and complement every non-apex variable. This is an exact
involution of all assignments, including isolated declared variables. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnsignedIsingRows
open Holant Holant.LocalDrafts.RemoteWork.HardnessChainV1
open BinaryCSPProgrammeCore
open scoped BigOperators
namespace R
export EOBinaryPlaneRaw (read value)
end R
namespace A
export BinaryIsingRows (rows expandedRows expanded_fst expanded_snd mixed_rows value_eq_mixed)
end A
namespace B
export BinaryIsingRaw (expanded expandedPolarities expanded_valid)
end B
namespace W
export BinaryIsingWeights (table interaction)
end W
namespace O
export EOBinaryPlaneOrient (flipWord)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def flip (n : ℕ) : Equiv.Perm (Fin (n+1)→Bool) where
  toFun z i := if i=0 then z i else !(z i)
  invFun z i := if i=0 then z i else !(z i)
  left_inv z := by funext i; by_cases hi : i=0 <;> simp [hi]
  right_inv z := by funext i; by_cases hi : i=0 <;> simp [hi]

theorem read_flip_zero {n : ℕ} (z : Fin (n+1)→Bool) : R.read (flip n z) 0=R.read z 0 := by
  simp [R.read,flip]

theorem read_flip_succ {n : ℕ} (z : Fin (n+1)→Bool) (i : ℕ) (hi : i<n) :
    R.read (flip n z) (i+1)=!(R.read z (i+1)) := by
  have hs : i+1<n+1 := by omega
  have hn : (⟨i+1,hs⟩ : Fin (n+1))≠0 := by
    intro zero
    have h := congrArg Fin.val zero
    simp only [Fin.val_zero] at h
    omega
  simp only [R.read,dif_pos hs]
  change (if (⟨i+1,hs⟩ : Fin (n+1))=0 then z ⟨i+1,hs⟩ else !(z ⟨i+1,hs⟩))=!(z ⟨i+1,hs⟩)
  rw [if_neg hn]

theorem row_flip (p q : K) (r : Raw) (hr : r.WellFormed) (k : ℕ)
    (z : Fin (r.variables+1)→Bool) (row : (ℕ×ℕ)×Bool) (member : row∈A.expandedRows r k) :
    W.table q p (O.flipWord ![row.2,false] ![R.read z row.1.1,R.read z row.1.2])=
      W.table p q ![R.read (flip r.variables z) row.1.1,R.read (flip r.variables z) row.1.2] := by
  obtain ⟨old,hold,hcopy⟩ := List.mem_flatMap.mp member
  have eqn := (List.mem_replicate.mp hcopy).2
  subst row
  obtain ⟨e,he,which⟩ := List.mem_flatMap.mp hold
  have bounds := hr.1 e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at which
  rcases which with rfl|rfl|rfl
  · rw [read_flip_succ z e.1 bounds.1,read_flip_zero]
    cases hx : R.read z (e.1+1) <;> cases ha : R.read z 0 <;>
      simp [W.table,W.interaction,O.flipWord,hx,ha]
  · rw [read_flip_succ z e.2 bounds.2,read_flip_zero]
    cases hy : R.read z (e.2+1) <;> cases ha : R.read z 0 <;>
      simp [W.table,W.interaction,O.flipWord,hy,ha]
  · rw [read_flip_succ z e.1 bounds.1,read_flip_succ z e.2 bounds.2]
    cases hx : R.read z (e.1+1) <;> cases hy : R.read z (e.2+1) <;>
      simp [W.table,W.interaction,O.flipWord,hx,hy]

theorem value_eq_unsigned (p q : K) (r : Raw) (hr : r.WellFormed) (k : ℕ) :
    BinaryIsingQuery.value q p (r,k)=R.value (W.table p q) (B.expanded r k) := by
  rw [A.value_eq_mixed q p r hr k,←A.expanded_snd]
  rw [A.mixed_rows _ _ _ (A.expandedRows r k) (A.expanded_fst r k)]
  change (∑z : Fin (r.variables+1)→Bool,_)=_
  calc
    _=∑z : Fin (r.variables+1)→Bool,
        ((A.expandedRows r k).map (fun row=>W.table p q
          ![R.read (flip r.variables z) row.1.1,R.read (flip r.variables z) row.1.2])).prod := by
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      apply List.map_congr_left
      intro row hrow
      exact row_flip p q r hr k z row hrow
    _=∑z : Fin (r.variables+1)→Bool,
        ((A.expandedRows r k).map (fun row=>W.table p q ![R.read z row.1.1,R.read z row.1.2])).prod :=
      Equiv.sum_comp (flip r.variables) (fun z : Fin (r.variables+1)→Bool=>
        ((A.expandedRows r k).map (fun row=>W.table p q ![R.read z row.1.1,R.read z row.1.2])).prod)
    _=R.value (W.table p q) (B.expanded r k) := by
      unfold R.value
      rw [←A.expanded_fst]
      simp only [List.map_map,Function.comp_def]
      rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnsignedIsingRows
end
