import Holant.Proofs.Hardness.GeneralEOAffinePlaneChainLabels

/-! Every physical vertex of the crossed chain retains the exact selected
original label, even when the original dictionary has coinciding signatures. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneChainOccurrences
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOAffinePlaneChain (copies literal)
end C
namespace L
export GeneralEOAffinePlaneChainLabels (copies literal)
end L
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s : ℕ} {a : ℕ→ℕ}

private theorem copies_labels (N : Network K 4) (l : Labelling N.shape s 1 a)
    (j : Fin s) (hl : ∀v,l.vertex v=j) (k : ℕ) :
    ∀v,(L.copies N l k).vertex v=j := by
  induction k with
  | zero => exact hl
  | succ k ih =>
      intro v
      change Sum.elim (L.copies N l k).vertex l.vertex (finSumFinEquiv.symm v)=j
      cases finSumFinEquiv.symm v with
      | inl v => exact ih v
      | inr v => exact hl v

variable (G : (i : Fin s)→Signature K (a i.val)) (j : Fin s)
variable (M : Signature K 4) (hM : (⟨a j.val,G j⟩ : AnySignature K)=⟨4,M⟩)
variable (e : Equiv.Perm (Fin 4))

theorem literal_labels (k : ℕ) : ∀v,(L.literal G j M hM e k).vertex v=j :=
  copies_labels _ _ j (fun _ => rfl) k

theorem template_labels (k : ℕ) :
    ∀row∈(L.literal G j M hM e k).template.vertices,row.1=j.val := by
  intro row hr
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
  exact congrArg Fin.val (literal_labels G j M hM e k v)

theorem exact_occurrences (k : ℕ) :
    ((L.literal G j M hM e k).template.vertices.filter (fun row => row.1==j.val)).length=k+1 := by
  rw [List.filter_eq_self.mpr]
  · exact GeneralEOAffinePlaneChainLabels.template_vertices G j M hM e k
  · intro row hr
    simp only [template_labels G j M hM e k row hr,beq_self_eq_true]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneChainOccurrences
